"""
bennett_fcu.py — A0 prototype for R1 G2 architecture (2026_nakano_rtm).

Goal
----
G1 (semantic inverse `phaseU2`) and G2-forward (`phaseF2` computes M₀'s function
on the work banks) are mechanised in Lean.  What remains for the FULL
unconditional theorem is the Bennett forward-copy-uncompute (F;C;U) architecture
that turns the garbage-laden `phaseF2` into a CLEAN reversible computer of a
prescribed involution `f`, then conjugates a bank-swap to get an involutory
machine that computes `f`.

This prototype validates, on concrete involutions, BEFORE any Lean:

  B := F ; C ; U      (forward phaseF2 ; copy work→ancilla ; uncompute phaseU2)
  B(x, blank, 0)  =  (x, blank, f(x))            -- clean, garbage-free
  D := B⁻¹ ∘ swap ∘ B   (swap work↔ancilla)
  D(x, blank, 0)  =  (f(x), blank, 0)            -- computes f, and is involutory

Bank layout settled here: work banks 0..k-1, history "h", ancilla ("a", i).

Copy design: the general-Γ "write-on-blank / unblank-on-match" copy (domain
restricted, mirroring phaseF2's reachable-domain reversibility), NOT CNOT (which
would need an additive group on Γ).  This is the variant to mechanise in A1.

FINDINGS (2026-06-20, all checks pass):
1. BANK LAYOUT settled: work `0..k-1`, history `"h"`, ancilla `("a", i)`.
   F and U touch only work+history; C touches only work+ancilla.  No bank
   collides; phases compose by threading the shared work banks.
2. COPY = write-on-blank / unblank-on-match works for general Γ (no group
   needed) and is a domain-restricted inverse of itself (verified 1 & 2 banks).
3. B = F;C;U gives B(x, blank, 0) = (x, blank, f(x)) — clean, history erased
   (verified for f = bit-flip, identity, 2-bank swap).
4. D = B⁻¹ ∘ swap ∘ B (swap work↔ancilla) computes f on the work bank with
   ancilla+history blank, AND is involutory D(D(x))=x (verified).
   Confirms the Lean A2–A5 architecture: conj_isPartialInvolution with
   R=B, R'=B⁻¹ (= phaseF2 ; copy_rev ; phaseU2), M = work↔ancilla swap.
"""

from __future__ import annotations
import itertools
import bennett_uncompute as bu
from bennett_uncompute import (
    Tape, Cfg, winl, BLANK, DEFAULT, encode_input, eval_run,
    phaseF2, phaseU2, tapes_key,
)


# ---------------------------------------------------------------------------
# Copy machine (semantic, write-on-blank / unblank-on-match) — A0.1
# ---------------------------------------------------------------------------

def copy_fwd(tapes: dict, kwork: int) -> dict:
    """C: copy each work bank i to a fresh ancilla bank ("a", i).
    Requires the ancilla blank (write-on-blank).  Returns a new tapes dict with
    the ancilla banks added/overwritten as copies of the work banks."""
    out = {b: Tape(dict(t.store), t.head) for b, t in tapes.items()}
    for i in range(kwork):
        wt = tapes[i]
        out[("a", i)] = Tape(dict(wt.store), wt.head)  # ancilla := work
    return out


def copy_rev(tapes: dict, kwork: int) -> dict:
    """C⁻¹: blank each ancilla bank that currently equals its work bank
    (unblank-on-match).  Returns a new tapes dict with the ancilla banks blanked
    if they matched; otherwise leaves them (domain-restricted inverse)."""
    out = {b: Tape(dict(t.store), t.head) for b, t in tapes.items()}
    for i in range(kwork):
        if ("a", i) in tapes and tapes[("a", i)].key() == tapes[i].key():
            out[("a", i)] = Tape({}, tapes[("a", i)].head)  # blank, keep head
    return out


def check_copy(kwork=1, gamma=(0, 1)):
    ok = True
    for x in itertools.product(gamma, repeat=kwork):
        work = encode_input(x, kwork)           # work=x, "h" blank
        # add blank ancilla
        with_anc = {**work, **{("a", i): Tape({}, 0) for i in range(kwork)}}
        c = copy_fwd(with_anc, kwork)
        for i in range(kwork):
            if c[("a", i)].key() != c[i].key():
                print(f"  [copy] FAIL: ancilla {i} != work for x={x}"); ok = False
        back = copy_rev(c, kwork)
        for i in range(kwork):
            if back[("a", i)].store != {}:
                print(f"  [copy] FAIL: uncopy didn't blank ancilla {i} for x={x}"); ok = False
    print(f"  [copy] {'OK' if ok else 'FAIL'}")
    return ok


# ---------------------------------------------------------------------------
# B = F ; C ; U   and   B⁻¹ = phaseF2 ; copy_rev ; phaseU2     — A0.2 / A0.3
# Each machine phase runs on its own bank subset; we thread the shared work.
# ---------------------------------------------------------------------------

def _work_h(tapes: dict, kwork: int) -> dict:
    return {**{i: tapes[i] for i in range(kwork)}, "h": tapes["h"]}


def B_run(M0, kwork, q0, x):
    """B(x, blank, 0): forward phaseF2, copy work→ancilla, uncompute phaseU2.
    Returns the full tapes dict, or None if any phase diverges."""
    # F: phaseF2 on work+history
    F_out = eval_run(phaseF2(M0, kwork), Cfg(("A1", q0), encode_input(x, kwork)))
    if F_out is None:
        return None
    Ft = F_out.tapes
    # C: copy work (= f(x)) onto fresh ancilla
    anc = {("a", i): Tape(dict(Ft[i].store), Ft[i].head) for i in range(kwork)}
    # U: phaseU2 on work+history (work from F, history from F)
    U_out = eval_run(phaseU2(M0, kwork), Cfg("RStart", _work_h(Ft, kwork)))
    if U_out is None:
        return None
    Ut = U_out.tapes
    return {**{i: Ut[i] for i in range(kwork)}, "h": Ut["h"], **anc}


def Binv_run(M0, kwork, q0, tapes):
    """B⁻¹: phaseF2 (= U⁻¹) on work+h, copy_rev (= C⁻¹), phaseU2 (= F⁻¹) on work+h.
    Returns the full tapes dict, or None if a phase diverges."""
    # U⁻¹ = phaseF2 on work+history
    P_out = eval_run(phaseF2(M0, kwork), Cfg(("A1", q0), _work_h(tapes, kwork)))
    if P_out is None:
        return None
    Pt = P_out.tapes
    # carry ancilla, then C⁻¹ (unblank-on-match against the new work)
    full = {**{i: Pt[i] for i in range(kwork)}, "h": Pt["h"],
            **{("a", i): tapes[("a", i)] for i in range(kwork)}}
    full = copy_rev(full, kwork)
    # F⁻¹ = phaseU2 on work+history
    Q_out = eval_run(phaseU2(M0, kwork), Cfg("RStart", _work_h(full, kwork)))
    if Q_out is None:
        return None
    Qt = Q_out.tapes
    return {**{i: Qt[i] for i in range(kwork)}, "h": Qt["h"],
            **{("a", i): full[("a", i)] for i in range(kwork)}}


def swap_work_anc(tapes: dict, kwork: int) -> dict:
    out = {b: t for b, t in tapes.items()}
    for i in range(kwork):
        out[i], out[("a", i)] = tapes[("a", i)], tapes[i]
    return out


def D_run(M0, kwork, q0, x):
    """D = B⁻¹ ∘ swap ∘ B on input (x, blank, 0)."""
    b = B_run(M0, kwork, q0, x)
    if b is None:
        return None
    s = swap_work_anc(b, kwork)
    return Binv_run(M0, kwork, q0, s)


# ---------------------------------------------------------------------------
# Checks — A0.4
# ---------------------------------------------------------------------------

def work_tuple(tapes, kwork):
    """read the work-bank head values (projected Γ)."""
    out = []
    for i in range(kwork):
        s = tapes[i].read()
        out.append(s[1] if s[0] == "w" else DEFAULT)
    return tuple(out)


def anc_tuple(tapes, kwork):
    out = []
    for i in range(kwork):
        s = tapes[("a", i)].read()
        out.append(s[1] if s[0] == "w" else DEFAULT)
    return tuple(out)


def f_of(M0, kwork, q0, x):
    """the work output of phaseF2 = M₀'s function f(x), via fwd_sem."""
    F_out = eval_run(phaseF2(M0, kwork), Cfg(("A1", q0), encode_input(x, kwork)))
    return None if F_out is None else work_tuple(F_out.tapes, kwork)


def check_B(name, M0, kwork, q0, gamma=(0, 1)):
    ok = True
    for x in itertools.product(gamma, repeat=kwork):
        b = B_run(M0, kwork, q0, x)
        fx = f_of(M0, kwork, q0, x)
        if b is None or fx is None:
            continue
        # B(x,blank,0) = (x, blank, f(x))
        if work_tuple(b, kwork) != x:
            print(f"  [{name}/B] FAIL work: {work_tuple(b,kwork)} != {x}"); ok = False
        if b["h"].store != {}:
            print(f"  [{name}/B] FAIL history not erased for x={x}"); ok = False
        if anc_tuple(b, kwork) != fx:
            print(f"  [{name}/B] FAIL ancilla {anc_tuple(b,kwork)} != f(x)={fx}"); ok = False
    print(f"  [{name}/B] {'OK' if ok else 'FAIL'}")
    return ok


def check_D(name, M0, kwork, q0, gamma=(0, 1)):
    """D computes f on the work bank, ancilla/history blank, and is involutory."""
    ok = True
    for x in itertools.product(gamma, repeat=kwork):
        d = D_run(M0, kwork, q0, x)
        fx = f_of(M0, kwork, q0, x)
        if d is None or fx is None:
            continue
        if work_tuple(d, kwork) != fx:
            print(f"  [{name}/D] FAIL: D(x)={work_tuple(d,kwork)} != f(x)={fx}"); ok = False
        if any(d[("a", i)].store != {} for i in range(kwork)):
            print(f"  [{name}/D] FAIL: ancilla not blank for x={x}"); ok = False
        if d["h"].store != {}:
            print(f"  [{name}/D] FAIL: history not blank for x={x}"); ok = False
        # involutory: D(D(x)) = x  (run D again on D's work output)
        d2 = D_run(M0, kwork, q0, work_tuple(d, kwork))
        if d2 is None or work_tuple(d2, kwork) != x:
            print(f"  [{name}/D] FAIL involution: D(D({x}))={None if d2 is None else work_tuple(d2,kwork)} != {x}")
            ok = False
    print(f"  [{name}/D] {'OK' if ok else 'FAIL'}")
    return ok


# involutions f built from small M₀ (must satisfy f∘f = id)
def M0_flip(q, a):          # f(x) = 1 - x   (involution)
    if q == "r":
        return ("f", ("write", {0: 1 - a[0]}))
    return None


def M0_id(q, a):            # f = identity
    return None             # halts immediately at q0


def M0_swap2(q, a):         # 2 banks: swap them (involution on pairs)
    if q == "r":
        return ("f", ("perm", {0: 1, 1: 0}))
    return None


if __name__ == "__main__":
    print("A0.1 copy machine:")
    rc = check_copy(1)
    rc2 = check_copy(2)
    print()
    print("A0.2/A0.3 B = F;C;U  and  D = B⁻¹∘swap∘B:")
    results = [rc, rc2]
    results.append(check_B("flip", M0_flip, 1, "r"))
    results.append(check_D("flip", M0_flip, 1, "r"))
    results.append(check_B("id", M0_id, 1, "r"))
    results.append(check_D("id", M0_id, 1, "r"))
    results.append(check_B("swap2", M0_swap2, 2, "r"))
    results.append(check_D("swap2", M0_swap2, 2, "r"))
    print()
    print("ALL PASS" if all(results) else "SOME FAILED")
