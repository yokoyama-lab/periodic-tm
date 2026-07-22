"""
finite_order.py — prototype for the "periodic Turing machine" paper
(2026_nakano_rtm).

Goal of this prototype
----------------------
Test, empirically, the *real* generalization of Nakano's Involutory Turing
Machines (ITM, f^2 = id) to finite order (f^n = id).

Key finding while attacking the completeness conjecture
-------------------------------------------------------
Nakano's ITM completeness rests on a Z/2-specific fact: reversing a reversible
Turing-machine run computes the INVERSE function, and the syntactic flip
symmetry  delta = flip_sigma(delta)  therefore forces  [[M]] = [[M]]^{-1},
i.e. an involution.  There is no "1/3 time reversal", so a Z/n state symmetry
does NOT force order n.  The naive cyclic-TM conjecture is the wrong handle.

The right handle is the dihedral identity "a rotation is the product of two
reflections", made *computable*: when f has finite order n, every orbit has
length m | n <= n, so the whole orbit {x, f(x), ..., f^{m-1}(x)} can be
enumerated, a canonical basepoint chosen, and two reflections (involutions)
i1, i2 defined with  f = i1 . i2.  Hence:

    THEOREM (provable).  For fixed n, every computable bijection f with
    f^n = id is the composition of two computable involutions i1, i2, each
    computable from f.  Equivalently, f is computed by the composition of two
    involutory Turing machines.

This file builds order-n computable bijections, derives i1, i2 by the orbit
construction, and verifies the theorem on many samples.  This is the n=3
"feel" requested before any nk-tape proof attempt.
"""

from __future__ import annotations
from typing import Callable, Iterable


# ---------------------------------------------------------------------------
# Orbit-based decomposition  f = i1 . i2  (the constructive heart)
# ---------------------------------------------------------------------------

def orbit(f: Callable[[int], int], x: int, n: int) -> list[int]:
    """Canonical orbit of x as the list [b, f(b), ..., f^{m-1}(b)] where the
    basepoint b = min(orbit) gives every element of the orbit a well-defined,
    x-independent position.  Requires f^n = id (so m | n, m <= n)."""
    seen = [x]
    y = f(x)
    steps = 0
    while y != x:
        seen.append(y)
        y = f(y)
        steps += 1
        if steps > n:  # safety: f is not actually order-dividing-n
            raise ValueError(f"orbit of {x} exceeds n={n}: f^n != id")
    b = min(seen)
    cyc = [b]
    z = f(b)
    while z != b:
        cyc.append(z)
        z = f(z)
    return cyc


def decompose(f: Callable[[int], int], n: int):
    """Return (i1, i2): two involutions with f = i1 . i2  (apply i2 then i1).

    On each orbit  cyc = [b, f(b), ..., f^{m-1}(b)]  put pos(cyc[j]) = j.
        i2 = reflection fixing b   : pos j  |-> pos (m - j) mod m
        i1 = f . i2                : pos j  |-> pos (j + 1) ... so f = i1 . i2
    Both are reflections of the cycle, hence involutions.
    """
    def positions(x: int):
        cyc = orbit(f, x, n)
        return cyc, {v: j for j, v in enumerate(cyc)}

    def i2(x: int) -> int:
        cyc, pos = positions(x)
        m = len(cyc)
        return cyc[(m - pos[x]) % m]

    def i1(x: int) -> int:
        # i1 = f . i2 in position space: pos j |-> pos (m - j + 1) mod m.
        # This is the *other* reflection of the cycle (about the "half-integer
        # axis"), hence an involution; composing with i2 gives the rotation f.
        cyc, pos = positions(x)
        m = len(cyc)
        return cyc[(m - pos[x] + 1) % m]

    return i1, i2


# A direct, self-contained i1 (= f . i2) avoids relying on the algebra above:
def decompose_checked(f: Callable[[int], int], n: int):
    _, i2 = decompose(f, n)
    i1 = lambda x: f(i2(x))   # by definition i1 := f . i2, manifestly making f = i1 . i2
    return i1, i2


# ---------------------------------------------------------------------------
# Example finite-order computable bijections
# ---------------------------------------------------------------------------

def f_rgb(x: int) -> int:
    """Order-3 'RGB rotation': partition Z into triples {3k,3k+1,3k+2} and
    cyclically rotate within each.  Infinitely many length-3 orbits."""
    k, r = divmod(x, 3)        # Python divmod handles negatives consistently
    return 3 * k + (r + 1) % 3


def f_mixed_order6(x: int) -> int:
    """Order-6 bijection mixing cycle lengths dividing 6:
       - x < 0 : fixed point            (cycle length 1)
       - x in {6k..6k+1}, k>=0: 2-cycle (swap)            (length 2)
       - x in {6k+2..6k+4}: 3-cycle (rotate)              (length 3)
       - x == 6k+5: fixed point                           (length 1)
    lcm(1,2,3) = 6, so f^6 = id but f^2 != id and f^3 != id."""
    if x < 0:
        return x
    k, r = divmod(x, 6)
    if r in (0, 1):
        return 6 * k + (1 - r)              # swap 6k <-> 6k+1
    if r in (2, 3, 4):
        return 6 * k + 2 + (r - 2 + 1) % 3  # rotate 6k+2 -> 6k+3 -> 6k+4 -> 6k+2
    return x                                 # r == 5 fixed


# ---------------------------------------------------------------------------
# Verification harness
# ---------------------------------------------------------------------------

def iterate(f: Callable[[int], int], x: int, k: int) -> int:
    for _ in range(k):
        x = f(x)
    return x


def verify(name: str, f: Callable[[int], int], n: int, sample: Iterable[int]) -> bool:
    sample = list(sample)
    ok = True

    # (1) f^n = id on the sample
    bad = [x for x in sample if iterate(f, x, n) != x]
    print(f"[{name}] f^{n} = id : {'OK' if not bad else f'FAIL at {bad[:5]}'}")
    ok &= not bad

    # (1b) n is the true order on the sample (no smaller divisor works), informational
    true_order = 1
    for x in sample:
        o = 1
        while iterate(f, x, o) != x:
            o += 1
        true_order = true_order * o // _gcd(true_order, o)  # lcm
    print(f"[{name}] observed order on sample = {true_order} (divides {n}: {n % true_order == 0})")

    # (2) build decomposition and check i1, i2 are involutions and f = i1 . i2
    # Test BOTH the closed-form i1 (reflection j -> m-j+1) and the definitional
    # i1 = f . i2, and that they agree — guards against the rotation-vs-
    # reflection bug where a wrong closed form hides behind the checked one.
    i1c, i2c = decompose(f, n)
    i1, i2 = decompose_checked(f, n)
    bad_i2 = [x for x in sample if i2(i2(x)) != x]
    bad_i1 = [x for x in sample if i1(i1(x)) != x]
    bad_cf = [x for x in sample if i1c(i1c(x)) != x]
    bad_ag = [x for x in sample if i1c(x) != i1(x) or i2c(x) != i2(x)]
    bad_fc = [x for x in sample if i1(i2(x)) != f(x)]
    print(f"[{name}] i2 involution (i2^2=id) : {'OK' if not bad_i2 else f'FAIL at {bad_i2[:5]}'}")
    print(f"[{name}] i1 involution (i1^2=id) : {'OK' if not bad_i1 else f'FAIL at {bad_i1[:5]}'}")
    print(f"[{name}] closed-form i1^2 = id   : {'OK' if not bad_cf else f'FAIL at {bad_cf[:5]}'}")
    print(f"[{name}] closed-form == f . i2   : {'OK' if not bad_ag else f'FAIL at {bad_ag[:5]}'}")
    print(f"[{name}] f = i1 . i2             : {'OK' if not bad_fc else f'FAIL at {bad_fc[:5]}'}")
    ok &= not (bad_i1 or bad_i2 or bad_cf or bad_ag or bad_fc)
    return ok


def _gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a


if __name__ == "__main__":
    R = range(-20, 41)
    all_ok = True
    print("=== order-3 RGB rotation ===")
    all_ok &= verify("rgb", f_rgb, 3, R)
    print()
    print("=== order-6 mixed (cycle lengths 1,2,3) ===")
    all_ok &= verify("mixed6", f_mixed_order6, 6, R)
    print()
    # Negative control: an order-3 function with the WRONG n must be caught.
    print("=== negative control: rgb claimed as order 2 (should FAIL f^2=id) ===")
    try:
        verify("rgb-as-2", f_rgb, 2, R)
    except ValueError as e:
        print(f"[rgb-as-2] correctly rejected: {e}")
    print()
    print("ALL CORE CHECKS:", "OK" if all_ok else "FAIL")
