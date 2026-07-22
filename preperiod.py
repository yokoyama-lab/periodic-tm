"""
preperiod.py — the eventually-periodic branch (pre-period m >= 1).

Validates Theorem (pre-period one): if f^{p+1} = f (i.e. f is (1,p)-periodic,
"index 1" in monogenic-semigroup terms), then

    f  =  g . e        where  e := f^p   (idempotent retraction onto the core)
                       and    g := f on the core Fix(f^p), identity elsewhere
                              (a bijection with g^p = id).

Combined with finite_order.decompose (finite order => two involutions):
    f = i1 . i2 . e    — two computable involutions and a computable idempotent.

Also sketches the m = 2 no-go shape: the halting-tail function whose image is
undecidable, while any g1 . e . g2 (computable bijections around one
computable idempotent) has decidable image.
"""

from __future__ import annotations
from typing import Callable, Iterable

from finite_order import decompose_checked, iterate


# ---------------------------------------------------------------------------
# The (1,p) construction
# ---------------------------------------------------------------------------

def core_idem(f: Callable[[int], int], p: int) -> Callable[[int], int]:
    """e := f^p — the canonical idempotent of a (1,p)-periodic f."""
    return lambda x: iterate(f, x, p)


def core_rot(f: Callable[[int], int], p: int) -> Callable[[int], int]:
    """g := f on the core Fix(f^p), identity elsewhere.

    For (1,p)-periodic f this is a bijection with g^p = id: the core is
    f-closed and f restricted to it is a disjoint union of cycles of length
    dividing p."""
    def g(x: int) -> int:
        return f(x) if iterate(f, x, p) == x else x
    return g


# ---------------------------------------------------------------------------
# Example (1,3)-periodic function on Z:
#   core = {0,1,2} with rotation 0 -> 1 -> 2 -> 0;
#   every other x is a depth-1 tail point mapping to (x mod 3).
# ---------------------------------------------------------------------------

def f_13(x: int) -> int:
    if x in (0, 1, 2):
        return (x + 1) % 3
    return x % 3          # Python % is nonnegative for positive modulus


def verify_preperiod_one(name: str, f, p: int, sample: Iterable[int]) -> bool:
    sample = list(sample)
    ok = True

    # (0) hypothesis: f^{p+1} = f
    bad = [x for x in sample if iterate(f, x, p + 1) != f(x)]
    print(f"[{name}] f^(p+1) = f          : {'OK' if not bad else f'FAIL at {bad[:5]}'}")
    ok &= not bad

    e, g = core_idem(f, p), core_rot(f, p)

    # (1) e idempotent
    bad = [x for x in sample if e(e(x)) != e(x)]
    print(f"[{name}] e = f^p idempotent   : {'OK' if not bad else f'FAIL at {bad[:5]}'}")
    ok &= not bad

    # (2) g^p = id
    bad = [x for x in sample if iterate(g, x, p) != x]
    print(f"[{name}] g^p = id             : {'OK' if not bad else f'FAIL at {bad[:5]}'}")
    ok &= not bad

    # (3) f = g . e
    bad = [x for x in sample if g(e(x)) != f(x)]
    print(f"[{name}] f = g . e            : {'OK' if not bad else f'FAIL at {bad[:5]}'}")
    ok &= not bad

    # (4) end-to-end: g = i1 . i2 (Theorem 1), hence f = i1 . i2 . e
    i1, i2 = decompose_checked(g, p)
    bad = [x for x in sample if i1(i2(e(x))) != f(x)]
    bad_i = [x for x in sample if i1(i1(x)) != x or i2(i2(x)) != x]
    print(f"[{name}] i1,i2 involutions    : {'OK' if not bad_i else f'FAIL at {bad_i[:5]}'}")
    print(f"[{name}] f = i1 . i2 . e      : {'OK' if not bad else f'FAIL at {bad[:5]}'}")
    ok &= not (bad or bad_i)
    return ok


# ---------------------------------------------------------------------------
# The m = 2 no-go shape (finite analogue of the halting-tail function):
# sources a_{n,s} -> b_n (if "machine n halts in exactly s steps") else -> c;
# b_n -> c; c -> c.  Here we only check it is (2,1)-periodic — the
# undecidability of its image is of course not testable, but the SHAPE shows
# pre-period exactly 2, which the (1,p) construction must reject.
# ---------------------------------------------------------------------------

def f_21_shape(x: int) -> int:
    # encode: c = 0; b_n = 2n+1 (n >= 0); a_k = 2k+2 (k >= 0), with a_k -> b_{k%3}
    # "halting" pattern stubbed by parity of k just to build the 2-level tails.
    if x == 0:
        return 0
    if x % 2 == 1:
        return 0                  # b_n -> c
    k = (x - 2) // 2
    return (2 * (k % 3) + 1) if k % 2 == 0 else 0   # a_k -> b or c


if __name__ == "__main__":
    R = range(-30, 61)
    ok = verify_preperiod_one("f13", f_13, 3, R)
    print()
    # (2,1) shape: f^3 = f^2 but f^2 != f  (pre-period exactly 2)
    f, sample = f_21_shape, range(0, 60)
    h1 = all(iterate(f, x, 3) == iterate(f, x, 2) for x in sample)
    h2 = any(iterate(f, x, 2) != f(x) for x in sample)
    print(f"[f21] f^3 = f^2 (period 1)   : {'OK' if h1 else 'FAIL'}")
    print(f"[f21] f^2 != f (pre-period 2): {'OK' if h2 else 'FAIL'}")
    # the (1,p) hypothesis must FAIL for this f (negative control)
    h3 = any(iterate(f, x, 2) != f(x) for x in sample)  # f^{1+1} != f
    print(f"[f21] (1,1) hypothesis fails : {'OK' if h3 else 'FAIL'}")
    print()
    print("ALL:", "OK" if ok and h1 and h2 and h3 else "FAIL")
