"""
copy_str.py — Option A prototype: reversible FULL-STRING traversal copy.

The single-cell `copyWA` (mechanised, `Copy.lean`) only copies the head, so the
F;C;U wrapper closes the unconditional theorem only for HEAD-VALUED data.  To
reach the GENERAL theorem we need a copy that duplicates the entire work string
onto a blank ancilla, reversibly, as an actual `KMachine` (alternating
write/move/perm steps — no abstract dict copy).

This prototype fixes that design and validates it BEFORE Lean:

  copyStr     : (W, A=blank, heads home)  ↦  (W, A=W, heads home)
  copyStrRev  : (W, A=W,     heads home)  ↦  (W, A=blank, heads home)

and checks the two domain-restricted inverse laws

  copyStrRev ∘ copyStr  = id   on  {A blank}
  copyStr   ∘ copyStrRev = id   on  {A = W}

DOMAIN.  The string is a BLANK-FREE contiguous block anchored at home: cells
0..n-1 are all non-blank, and cells -1 and n are blank.  The traversal detects the
string's right end by the terminating blank at n, so an internal blank would be
mistaken for the end — hence "blank-free" (this is exactly why a fully general
copy needs a delimiter/length scheme; see FINDING below).  The Lean version will
carry "blank-free contiguous block + blank ancilla" as the copy's `DomIn`, just
as `copyWA` carried `AncBlank`.

For the unconditional theorem this restricts the source machine's outputs to a
blank-free encoding (a delimiter alphabet, or a unary/length-prefixed code).  That
is a strictly larger class than the head-valued (single-cell) one already closed,
and removes the single-cell limitation for blank-free string data.

DESIGN (states, one KStmt per step; banks: work `0`, ancilla `("a",0)`).
Forward copyStr:
  C  : read w.  w≠blank → write A:=w, goto Cm.   w=blank → move both L, goto R.
  Cm : move both R, goto C.
  R  : read w.  w≠blank → move both L, stay R.    w=blank → move both R, goto done.
  done: halt.
Reverse copyStrRev: identical control, but C writes A:=blank (unblank) instead of
A:=w.  The return sweep R is driven by the UNCHANGED work tape, so it retraces
the same path; reversibility is the write-on-blank / unblank-on-match duality,
the same principle as the single-cell copy.
"""

from __future__ import annotations
from bennett_uncompute import Tape, Cfg, BLANK, apply_stmt

W = 0
A = ("a", 0)


def _delta(write_val):
    """Build the copy delta.  `write_val(w)` is what to write on the ancilla at a
    work cell reading `w`: `lambda w: w` to copy, `lambda w: BLANK` to unblank."""
    def delta(q, heads):
        w = heads[W]
        if q == "C":
            if w == BLANK:
                return ("R", ("move", {W: "L", A: "L"}))
            return ("Cm", ("write", {A: write_val(w)}))
        if q == "Cm":
            return ("C", ("move", {W: "R", A: "R"}))
        if q == "R":
            if w == BLANK:
                return ("done", ("move", {W: "R", A: "R"}))
            return ("R", ("move", {W: "L", A: "L"}))
        return None  # done
    return delta


copyStr_delta = _delta(lambda w: w)
copyStrRev_delta = _delta(lambda w: BLANK)


def run(delta, tapes, max_steps=10000):
    q, tp = "C", {b: Tape(dict(t.store), t.head) for b, t in tapes.items()}
    for _ in range(max_steps):
        heads = {b: t.read() for b, t in tp.items()}
        out = delta(q, heads)
        if out is None:
            return tp
        q, stmt = out
        tp = apply_stmt(tp, stmt)
    raise RuntimeError("did not halt")


def mk(work_cells):
    """Work tape holding `work_cells` (a list of Γ symbols, encoded winl) at
    positions 0..n-1, ancilla blank, both heads at 0."""
    from bennett_uncompute import winl
    wstore = {i: winl(c) for i, c in enumerate(work_cells) if c != 0}
    return {W: Tape(wstore, 0), A: Tape({}, 0)}


def tapes_key(tp):
    return tuple(sorted((str(b), t.key()) for b, t in tp.items()))


def check(work_cells):
    src = mk(work_cells)
    # forward: A becomes a copy of W; W unchanged; heads home
    fwd = run(copyStr_delta, src)
    ok_w = fwd[W].key() == src[W].key()
    ok_a = {k: v for k, v in fwd[A].store.items()} == {k: v for k, v in src[W].store.items()}
    ok_home = fwd[W].head == 0 and fwd[A].head == 0
    # round-trip: uncopy returns to blank ancilla
    back = run(copyStrRev_delta, fwd)
    ok_round = tapes_key(back) == tapes_key(src)
    # other inverse law: copyStr ∘ copyStrRev = id on {A = W}
    aw = {W: Tape(dict(src[W].store), 0), A: Tape(dict(src[W].store), 0)}
    aw_back = run(copyStrRev_delta, aw)
    aw_fwd = run(copyStr_delta, aw_back)
    ok_round2 = tapes_key(aw_fwd) == tapes_key(aw)
    return ok_w, ok_a, ok_home, ok_round, ok_round2


if __name__ == "__main__":
    # In-domain: blank-free contiguous blocks (and the empty block).
    cases = [
        [],                      # empty
        [1],                     # single cell
        [1, 2, 3],               # block
        [2, 2, 2, 2],            # repeats
        [3, 1, 4, 1, 5, 9, 2],   # longer
    ]
    allok = True
    for c in cases:
        okw, oka, okh, okr, okr2 = check(c)
        good = okw and oka and okh and okr and okr2
        allok = allok and good
        print(f"{str(c):24} W-kept={okw} A=copy={oka} home={okh} "
              f"uncopy={okr} copy∘uncopy={okr2}  {'OK' if good else 'FAIL'}")
    print("ALL PASS" if allok else "SOME FAILED")

    # Out-of-domain demonstration: an internal blank is read as the end, so the
    # copy is truncated — this is the documented limitation, not a bug.
    okw, oka, *_ = check([1, 0, 2])
    print(f"\n[out-of-domain] [1,0,2] internal blank: A=full-copy={oka} "
          f"(expected False — truncated at the internal blank)")
    assert allok and not oka, "in-domain must pass; internal-blank must truncate"
    print("PROTOTYPE VALIDATED")
