"""
bennett_uncompute.py — prototype for R1 Stage 1 (2026_nakano_rtm).

Goal
----
The descriptor-encoding Bennett simulator `phaseF2` (BennettReversible.lean) is
semantically reversible and computes an injective partial function
(`phaseF2_ktapeSem_inj`).  The R2 bridge (`SemReversible.lean`) reduced the
unconditional symmetrisation to ONE obligation: exhibit an inverse *machine*
`R'` with `SemInverse (phaseF2 M₀) R'`, i.e.

    Y ∈ ⟦phaseF2 M₀⟧ X   ↔   X ∈ ⟦R'⟧ Y .

This file builds `phaseF2` faithfully (same 4-state A1/S/S2/C cycle, same
shared alphabet Γ ⊕ HistEntry, same history bank) and a candidate uncompute
machine `phaseU2`, then tests the SemInverse relation on small M₀ over all
inputs.  Stage 1a question it answers empirically:

  * does an EXPLICIT reverse simulator invert phaseF2's semantics?
  * is SemInverse unrestricted (∀ X Y) or only on well-formed / reachable Y?
    (this decides the exact shape of the Lean statement)

FINDINGS (2026-06-20)
---------------------
1. Stage 1a = option (i) CONFIRMED.  An EXPLICIT reverse machine `phaseU2`
   (states RStart/RB/RC/RD/RFin, mirroring C/S2/S/A1 backwards) inverts
   `phaseF2` on every reachable output: rev(fwd(X)) = X and fwd(rev(fwd(X))) =
   fwd(X) for all small M₀ (write / move / perm / multi-step / mixed).  This is
   the concrete rule set to mechanise in Stage 1.

2. SemInverse MUST be DOMAIN-RESTRICTED.  The unrestricted relation
   (∀ X Y, Y ∈ ⟦phaseF2⟧ X ↔ X ∈ ⟦phaseU2⟧ Y) is FALSE: on non-reachable Y
   (work-cell history junk, history head not at the right end, blank gaps)
   `phaseU2` halts with a spurious X for which fwd(X) ≠ Y.  This is the same
   shared-alphabet/junk + head-geometry obstruction that forced WF + HistInv in
   the forward proof.  => the Lean `SemInverse` (currently ∀ X Y in
   SemReversible.lean) needs a domain predicate (reachable/WF/blank-history Y),
   and `conj_partial_involution_sem` must be re-proved tracking that the
   conjugation legs stay in-domain (WF preservation through R, M, R').

Faithfulness note
-----------------
phaseF2 tapes are indexed by ι ⊕ Fin 1: work banks (Sum.inl i) + one history
bank (Sum.inr 0).  Alphabet BennettAlph2 = Γ ⊕ HistEntry2; blank = Sum.inl
default.  We mirror the Lean `phaseF2` `match` exactly.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Callable, Optional
import itertools

# ---------------------------------------------------------------------------
# Tape model: bi-infinite tape as dict + head, with a blank default.
# ---------------------------------------------------------------------------

DEFAULT = 0  # the Γ blank value


def winl(g):
    """Sum.inl g — a work symbol."""
    return ("w", g)


def hstep(q, a):
    """Sum.inr (HistEntry2.step q a) — a descriptor.  a is a tuple."""
    return ("h", ("step", q, tuple(a)))


BLANK = winl(DEFAULT)  # Sum.inl default


@dataclass
class Tape:
    store: dict = field(default_factory=dict)
    head: int = 0

    def read(self):
        return self.store.get(self.head, BLANK)

    def write(self, sym):
        t = Tape(dict(self.store), self.head)
        if sym == BLANK:
            t.store.pop(t.head, None)
        else:
            t.store[t.head] = sym
        return t

    def move(self, d):
        if d is None:
            return Tape(dict(self.store), self.head)
        return Tape(dict(self.store), self.head + (1 if d == "R" else -1))

    def key(self):
        # canonical comparable form (drop blanks already absent)
        return (tuple(sorted(self.store.items())), self.head)


def revdir(d):
    if d is None:
        return None
    return "L" if d == "R" else "R"


# ---------------------------------------------------------------------------
# Configurations and the generic step / eval over a set of banks.
# A machine is  delta : (state, headvec) -> Optional[(state, stmt)]
# headvec : dict bank -> sym ;  stmt one of:
#   ("write", {bank: sym}) | ("move", {bank: dir|None}) | ("perm", perm)
# perm : dict bank -> bank  (a bijection on banks)
# ---------------------------------------------------------------------------

@dataclass
class Cfg:
    q: object
    tapes: dict  # bank -> Tape

    def heads(self):
        return {b: t.read() for b, t in self.tapes.items()}

    def key(self):
        return (self.q, tuple(sorted(((str(b), t.key()) for b, t in self.tapes.items()))))


def apply_stmt(tapes: dict, stmt) -> dict:
    kind = stmt[0]
    if kind == "write":
        vec = stmt[1]
        return {b: (t.write(vec[b]) if b in vec else t) for b, t in tapes.items()}
    if kind == "move":
        dvec = stmt[1]
        return {b: t.move(dvec.get(b)) for b, t in tapes.items()}
    if kind == "perm":
        perm = stmt[1]
        # tape at bank b after perm is the old tape at perm^{-1}(b)
        inv = {v: k for k, v in perm.items()}
        return {b: tapes[inv[b]] for b in tapes}
    raise ValueError(stmt)


def step(delta, c: Cfg) -> Optional[Cfg]:
    r = delta(c.q, c.heads())
    if r is None:
        return None
    q2, stmt = r
    return Cfg(q2, apply_stmt(c.tapes, stmt))


def eval_run(delta, c: Cfg, cap=10000) -> Optional[Cfg]:
    """Run to a halting config (delta = None) and return it; None if it loops
    past cap (deterministic, so cap just guards nontermination)."""
    seen = set()
    for _ in range(cap):
        k = c.key()
        if k in seen:
            return None  # loop -> diverges
        seen.add(k)
        nxt = step(delta, c)
        if nxt is None:
            return c
        c = nxt
    return None


# ---------------------------------------------------------------------------
# phaseF2 — faithful port of BennettReversible.lean (A1/S/S2/C).
# banks: work banks are ints 0..k-1 ; history bank is the string "h".
# ---------------------------------------------------------------------------

def read_work(heads, kwork):
    """project the Sum.inl component of each work head (a : ι → Γ)."""
    a = []
    for i in range(kwork):
        s = heads[i]
        a.append(s[1] if s[0] == "w" else DEFAULT)
    return tuple(a)


def phaseF2(M0, kwork):
    """M0 : (q, a_tuple) -> None | (q', stmt0) where stmt0 over work banks:
       ("write", tuple) | ("move", tuple of dir|None) | ("perm", perm-on-work)."""
    def delta(s, heads):
        tag = s[0]
        if tag == "A1":
            q = s[1]
            a = read_work(heads, kwork)
            r = M0(q, a)
            if r is None:
                return None
            _, stmt0 = r
            if stmt0[0] == "write":
                bp = stmt0[1]
                vec = {i: winl(bp[i]) for i in range(kwork)}
                vec["h"] = heads["h"]  # history stays as-is
                return (("S", q, a), ("write", vec))
            else:  # move / perm : identity write, carry (q,a)
                vec = dict(heads)
                return (("S", q, a), ("write", vec))
        if tag == "S":
            _, q, a = s
            r = M0(q, a)
            if r is None:
                return None
            _, stmt0 = r
            if stmt0[0] == "write":
                return (("S2", q, a), ("move", {}))  # no-op move
            if stmt0[0] == "move":
                d = stmt0[1]
                dvec = {i: d[i] for i in range(kwork)}
                dvec["h"] = None
                return (("S2", q, a), ("move", dvec))
            if stmt0[0] == "perm":
                pi = stmt0[1]  # perm on work banks
                perm = dict(pi)
                perm["h"] = "h"  # sumCongr pi (refl)
                return (("S2", q, a), ("perm", perm))
        if tag == "S2":
            _, q, a = s
            r = M0(q, a)
            if r is None:
                return None
            qp, _ = r
            h = heads["h"]
            if h[0] == "w":
                if h[1] == DEFAULT:  # blank history cell -> write descriptor
                    vec = {"h": hstep(q, a)}  # work stays put
                    return (("C", qp), ("write", vec))
                return None
            return None  # history cell already a descriptor
        if tag == "C":
            qp = s[1]
            return (("A1", qp), ("move", {"h": "R"}))
        raise ValueError(s)
    return delta


# ---------------------------------------------------------------------------
# phaseU2 — candidate uncompute (reverse) machine.
# States: RStart | (RC,q,a) | (RD,q,a) | RFin
# Mirrors phaseF2 backwards: seek-left, read descriptor, erase, undo work-op,
# restore old heads.  Halts with head back at history position 0, blanks erased.
# ---------------------------------------------------------------------------

def phaseU2(M0, kwork):
    def delta(s, heads):
        tag = s if isinstance(s, str) else s[0]
        if tag == "RStart":
            # move history head one step LEFT to inspect the previous descriptor
            return ("RB", ("move", {"h": "L"}))
        if tag == "RB":
            h = heads["h"]
            if h[0] == "h":  # a descriptor step(q,a)
                _, (_, q, a) = h
                # erase the descriptor (write blank on history cell)
                return (("RC", q, a), ("write", {"h": BLANK}))
            else:
                # blank: we have passed history position 0 -> reposition + halt
                return ("RFin", ("move", {"h": "R"}))
        if tag == "RC":
            _, q, a = s
            r = M0(q, a)
            assert r is not None, "descriptor for a halting state?"
            _, stmt0 = r
            # undo the forward S work-op
            if stmt0[0] == "write":
                return (("RD", q, a), ("move", {}))  # forward S was no-op
            if stmt0[0] == "move":
                d = stmt0[1]
                dvec = {i: revdir(d[i]) for i in range(kwork)}
                return (("RD", q, a), ("move", dvec))
            if stmt0[0] == "perm":
                pi = stmt0[1]
                inv = {v: k for k, v in pi.items()}
                perm = dict(inv)
                perm["h"] = "h"
                return (("RD", q, a), ("perm", perm))
        if tag == "RD":
            _, q, a = s
            r = M0(q, a)
            _, stmt0 = r
            # undo forward A1's work write
            if stmt0[0] == "write":
                vec = {i: winl(a[i]) for i in range(kwork)}  # restore old heads
                return ("RStart", ("write", vec))
            else:
                return ("RStart", ("move", {}))  # A1 was identity write
        if tag == "RFin":
            return None  # halt
        raise ValueError(s)
    return delta


# ---------------------------------------------------------------------------
# Encodings: input/output tapes for SemInverse testing.
# ---------------------------------------------------------------------------

def encode_input(T, kwork):
    """work tapes from a tuple T (one symbol per work bank, head at 0),
       blank history."""
    tapes = {}
    for i in range(kwork):
        tapes[i] = Tape({0: winl(T[i])} if T[i] != DEFAULT else {}, 0)
    tapes["h"] = Tape({}, 0)
    return tapes


def tapes_key(tapes):
    return tuple(sorted((str(b), t.key()) for b, t in tapes.items()))


def fwd_sem(M0, kwork, q0, in_tapes):
    """⟦phaseF2 M0⟧ from A1 q0 on in_tapes -> output tapes (or None)."""
    c = eval_run(phaseF2(M0, kwork), Cfg(("A1", q0), in_tapes))
    return None if c is None else c.tapes


def rev_sem(M0, kwork, in_tapes):
    """⟦phaseU2 M0⟧ from RStart on in_tapes -> output tapes (or None)."""
    c = eval_run(phaseU2(M0, kwork), Cfg("RStart", in_tapes))
    return None if c is None else c.tapes


# ---------------------------------------------------------------------------
# Test harness
# ---------------------------------------------------------------------------

def all_inputs(kwork, gamma):
    for combo in itertools.product(gamma, repeat=kwork):
        yield combo


def check_seminverse(name, M0, kwork, q0, gamma, verbose=False):
    """Test:  Y = fwd(X)  =>  rev(Y) = X   (forward leg of SemInverse), and
       on reachable Y, rev recovers a unique X with fwd(X)=Y."""
    ok = True
    n_tested = 0
    for X in all_inputs(kwork, gamma):
        in_tapes = encode_input(X, kwork)
        Y = fwd_sem(M0, kwork, q0, in_tapes)
        if Y is None:
            if verbose:
                print(f"  [{name}] fwd diverges on {X}")
            continue
        n_tested += 1
        Xback = rev_sem(M0, kwork, Y)
        if Xback is None:
            print(f"  [{name}] FAIL: rev(fwd({X})) diverged")
            ok = False
            continue
        if tapes_key(Xback) != tapes_key(in_tapes):
            print(f"  [{name}] FAIL: rev(fwd({X})) != X")
            print(f"        X      = {tapes_key(in_tapes)}")
            print(f"        rev(Y) = {tapes_key(Xback)}")
            ok = False
        # round-trip the other way: fwd(rev(Y)) should be Y
        Y2 = fwd_sem(M0, kwork, q0, Xback)
        if Y2 is None or tapes_key(Y2) != tapes_key(Y):
            print(f"  [{name}] FAIL: fwd(rev(fwd({X}))) != fwd({X})")
            ok = False
    print(f"  [{name}] {'OK' if ok else 'FAIL'}  ({n_tested} inputs round-tripped)")
    return ok


# ---------- Example M₀ machines (over work banks) ----------

def M0_write(q, a):
    """1 work bank. q0='r': flip the bit (write 1-a0), go to halt 'f'."""
    if q == "r":
        return ("f", ("write", {0: 1 - a[0]}))
    return None  # 'f' halts


def M0_move(q, a):
    """1 work bank. r: write a0 (identity) then... we need a move rule.
       r: move right, -> m ; m: halt.  (pure move, no symbol change)."""
    if q == "r":
        return ("m", ("move", {0: "R"}))
    return None


def M0_two_step(q, a):
    """1 work bank, two steps: r:write 1-a0 -> s ; s: move R -> f ; f halt."""
    if q == "r":
        return ("s", ("write", {0: 1 - a[0]}))
    if q == "s":
        return ("f", ("move", {0: "R"}))
    return None


def M0_perm(q, a):
    """2 work banks. r: swap banks (perm 0<->1) -> f ; f halt."""
    if q == "r":
        return ("f", ("perm", {0: 1, 1: 0}))
    return None


def M0_perm_then_write(q, a):
    """2 work banks. r: perm swap -> s ; s: write (a0+1 mod 2, a1) -> f."""
    if q == "r":
        return ("s", ("perm", {0: 1, 1: 0}))
    if q == "s":
        return ("f", ("write", {0: 1 - a[0], 1: a[1]}))
    return None


def check_domain_restriction():
    """KEY STAGE-1a FINDING.  Unrestricted SemInverse (∀ X Y) is FALSE for the
    explicit reverse machine: on non-reachable Y (work-cell junk, shifted head,
    blank gaps) `rev` halts with a spurious X for which fwd(X) != Y.  So the
    Lean `SemInverse` (currently ∀ X Y in SemReversible.lean) must be
    DOMAIN-RESTRICTED to reachable / well-formed Y — the same WF/HistInv
    restriction the forward injectivity proof needed."""
    M0, kwork, q0 = M0_two_step, 1, "r"
    fwd = lambda t: fwd_sem(M0, kwork, q0, t)
    rev = lambda t: rev_sem(M0, kwork, t)
    cases = [
        ("work-cell junk descriptor",
         {0: Tape({0: hstep("r", (0,))}, 0), "h": Tape({}, 0)}),
        ("history head on a descriptor (shifted)",
         {0: Tape({0: winl(1)}, 0), "h": Tape({0: ("h", ("step", "r", (0,)))}, 0)}),
        ("descriptors with a blank gap",
         {0: Tape({0: winl(0)}, 1),
          "h": Tape({-1: ("h", ("step", "r", (0,))), 1: ("h", ("step", "s", (1,)))}, 1)}),
    ]
    print("Domain-restriction probe (non-reachable Y):")
    violations = 0
    for name, Y in cases:
        try:
            X = rev(Y)
        except AssertionError:
            print(f"  [{name}] rev hits a halting-state descriptor (diverges) -- OK")
            continue
        if X is None:
            print(f"  [{name}] rev diverges (no spurious X) -- OK")
            continue
        Y2 = fwd(X)
        faithful = (Y2 is not None and tapes_key(Y2) == tapes_key(Y))
        print(f"  [{name}] rev halts; fwd(rev(Y))==Y ? {faithful}")
        if not faithful:
            violations += 1
    print(f"  => {violations} unrestricted-SemInverse violations "
          f"({'restriction REQUIRED' if violations else 'total'})")
    return violations


if __name__ == "__main__":
    G2 = [0, 1]
    print("SemInverse round-trip tests (phaseU2 inverts phaseF2 on reachable Y):")
    results = []
    results.append(check_seminverse("write", M0_write, 1, "r", G2))
    results.append(check_seminverse("move", M0_move, 1, "r", G2))
    results.append(check_seminverse("two_step", M0_two_step, 1, "r", G2))
    results.append(check_seminverse("perm", M0_perm, 2, "r", G2))
    results.append(check_seminverse("perm_then_write", M0_perm_then_write, 2, "r", G2))
    print()
    print("ALL ROUND-TRIPS PASS" if all(results) else "SOME FAILED")
    print()
    check_domain_restriction()
