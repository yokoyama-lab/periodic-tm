#!/usr/bin/env python3
"""
query_lb_search.py — exact minimax search for the query complexity of the
orbit-preserving two-involution decomposition (research/02-complexity.md,
Conjecture 2.3 / the "orbit-preserving ⌈(ℓ−1)/2⌉" foothold).

THE GAME (implemented exactly, no heuristics)
---------------------------------------------
Fix N (domain [N] = {0..N-1}), n (order: f^n = id), and x0 = 0.
Optionally a promise: the f-orbit of x0 has length exactly ℓ.

* The ALGORITHM adaptively queries points x, learning f(x).
* The ADVERSARY answers so that the transcript stays consistent with at
  least one permutation f of [N] with f^n = id (and the promise, if any).
* After q queries the algorithm outputs a value.  It WINS at depth q iff
  for EVERY f consistent with the transcript there is SOME valid
  orbit-preserving reflection ι₂ of f (ι₂ maps every f-orbit to itself,
  ι₂² = id, and ι₁ := f∘ι₂ satisfies ι₁² = id, i.e. ι₂ f ι₂ = f⁻¹ on
  every orbit) whose value(s) at the designated point(s) match the output.

Two designated-point sets are measured:

* Game A (single point, the literal task statement): output v, win iff
  ∀ consistent f ∃ valid ι₂ with ι₂(0) = v.
* Game B (two points, closer to the "global consistency" that Conjecture
  2.3 actually needs): output a pair (v0, v1), win iff ∀ consistent f
  ∃ a SINGLE valid ι₂ with ι₂(0) = v0 AND ι₂(1) = v1.

Game A collapses (see the LEMMA below): on an ℓ-cycle (a_0 … a_{ℓ-1})
the valid restrictions of ι₂ are EXACTLY the ℓ dihedral reflections
ι(a_i) = a_{(m-i) mod ℓ}, one of which (m = 0) fixes a_0.  So v = x0 is
a winning output with ZERO queries for every f.  The lemma is verified
by brute force in self_test(); Game A's value is therefore computed as 0
structurally (pass --paranoid to re-verify by exhaustive enumeration of
all consistent f for small N).  Game B does not collapse and is searched
by full minimax.

VALUE = exact minimax over the game tree:
  value(T) = 0                                  if the win test holds at T
           = 1 + min over queries x
                 max over consistent answers y  of value(T ∪ {x↦y})
with memoization on states canonicalized up to relabeling of all points
other than the designated ones (untouched points are interchangeable;
the known part of f is a disjoint union of paths and cycles, so a
canonical key is the multiset of path/cycle shapes with designated-point
flags, plus the count of untouched points).

The win test enumerates ALL consistent completions f (backtracking with
an exact feasibility filter for f^n = id and the ℓ-promise) and
intersects the sets of achievable output tuples; it is exact.

Run:  python3 research/query_lb_search.py            (full table, N=4..9)
      python3 research/query_lb_search.py --selftest (correctness checks)
      python3 research/query_lb_search.py --paranoid (also re-verify Game A
                                                      by enumeration, small N)
No external dependencies.
"""

import sys
import time
from functools import lru_cache

TIME_CAP = 150.0  # seconds per table cell; exceeded cells are reported as t/o


class Timeout(Exception):
    pass


@lru_cache(maxsize=None)
def divisors(n):
    return tuple(d for d in range(1, n + 1) if n % d == 0)


# ----------------------------------------------------------------------
# Structure of a transcript T (partial injective map x -> f(x)):
# the known part of f is a disjoint union of directed paths and cycles.
# ----------------------------------------------------------------------

def components(T, N):
    """Return (paths, cycles, untouched).
    paths:  list of node lists [p0,...,pk] with T[p_i]=p_{i+1}, f(p_k) unknown.
    cycles: list of node lists forming closed cycles.
    untouched: points appearing nowhere in T."""
    pred = {y: x for x, y in T.items()}
    nodes = set(T) | set(T.values())
    untouched = [v for v in range(N) if v not in nodes]
    seen, paths, cycles = set(), [], []
    for s in sorted(nodes):
        if s in seen or s in pred:
            continue
        comp, cur = [s], s
        while cur in T:
            cur = T[cur]
            comp.append(cur)
        seen |= set(comp)
        paths.append(comp)
    for s in sorted(nodes):
        if s in seen:
            continue
        comp, cur = [s], T[s]
        while cur != s:
            comp.append(cur)
            cur = T[cur]
        seen |= set(comp)
        cycles.append(comp)
    return paths, cycles, untouched


# ----------------------------------------------------------------------
# Exact consistency test:  does some permutation f ⊇ T with f^n = id
# (and orbit(0) of length exactly `promise`, if given) exist?
# Paths of s nodes and untouched singletons must be assembled into
# cycles whose lengths divide n.  Since 1 | n, leftover untouched points
# can always become fixed points.
# ----------------------------------------------------------------------

def _feasible_groups(sizes, u, n, forced=None):
    """sizes: tuple of open-path node counts (item 0 is the 0-component when
    forced is not None, in which case its group must total exactly `forced`).
    u: number of untouched points usable as padding.  True iff the paths can
    be partitioned into groups, each padded with untouched points up to a
    length dividing n (item 0's group padded to exactly `forced`)."""
    sizes = list(sizes)
    if forced is not None:
        s0 = sizes[0]
        rest = sizes[1:]
        m = len(rest)
        for mask in range(1 << m):
            tot = s0 + sum(rest[i] for i in range(m) if mask >> i & 1)
            pad = forced - tot
            if 0 <= pad <= u:
                rem = tuple(rest[i] for i in range(m) if not mask >> i & 1)
                if _feasible_groups(rem, u - pad, n):
                    return True
        return False
    if not sizes:
        return True  # remaining untouched points become fixed points (1 | n)
    s0, rest = sizes[0], sizes[1:]
    m = len(rest)
    for mask in range(1 << m):
        tot = s0 + sum(rest[i] for i in range(m) if mask >> i & 1)
        for d in divisors(n):
            pad = d - tot
            if 0 <= pad <= u:
                rem = tuple(rest[i] for i in range(m) if not mask >> i & 1)
                if _feasible_groups(rem, u - pad, n):
                    return True
    return False


def consistent(T, N, n, promise):
    paths, cycles, untouched = components(T, N)
    zero_cycle = zero_path = None
    for c in cycles:
        if n % len(c) != 0:
            return False
        if 0 in c:
            zero_cycle = c
    for p in paths:
        if len(p) > n:
            return False
        if 0 in p:
            zero_path = p
    if promise is not None:
        if zero_cycle is not None:
            if len(zero_cycle) != promise:
                return False
            return _feasible_groups(tuple(len(p) for p in paths),
                                    len(untouched), n)
        u = len(untouched)
        if zero_path is not None:
            if len(zero_path) > promise:
                return False
            sizes = (len(zero_path),) + tuple(len(p) for p in paths
                                              if p is not zero_path)
            return _feasible_groups(sizes, u, n, forced=promise)
        # 0 is untouched: treat it as a forced 1-node "path"
        sizes = (1,) + tuple(len(p) for p in paths)
        return _feasible_groups(sizes, u - 1, n, forced=promise)
    return _feasible_groups(tuple(len(p) for p in paths), len(untouched), n)


# ----------------------------------------------------------------------
# Enumeration of ALL consistent completions (exact win test uses this).
# ----------------------------------------------------------------------

def completions(T, N, n, promise, deadline):
    """Yield every permutation f (as a dict) with f ⊇ T, f^n = id, and the
    ℓ-promise if given.  Backtracking, pruned by the exact feasibility test."""
    if time.monotonic() > deadline:
        raise Timeout
    if len(T) == N:
        yield dict(T)
        return
    x = min(v for v in range(N) if v not in T)
    has_pred = set(T.values())
    for y in range(N):
        if y in has_pred:
            continue
        T[x] = y
        if consistent(T, N, n, promise):
            yield from completions(T, N, n, promise, deadline)
        del T[x]


# ----------------------------------------------------------------------
# Valid outputs for a fully known f.
# LEMMA (verified in self_test): the restrictions to an ℓ-cycle
# (a_0 … a_{ℓ-1}) of the valid orbit-preserving ι₂ are exactly the ℓ
# reflections ι(a_i) = a_{(m-i) mod ℓ}, m = 0..ℓ-1; reflections on
# distinct orbits are chosen independently.
# ----------------------------------------------------------------------

def orbit_of(f, x):
    orb, cur = [x], f[x]
    while cur != x:
        orb.append(cur)
        cur = f[cur]
    return orb


def valid_outputs(f, two_point):
    """Set of achievable outputs: {(v,)} for Game A, {(v0, v1)} for Game B."""
    orb0 = orbit_of(f, 0)
    if not two_point:
        return {(v,) for v in orb0}  # every reflection center is achievable
    L = len(orb0)
    if 1 in orb0:
        j = orb0.index(1)
        return {(orb0[m], orb0[(m - j) % L]) for m in range(L)}
    orb1 = orbit_of(f, 1)
    return {(a, b) for a in orb0 for b in orb1}


def valid_outputs_bruteforce(f, N, two_point):
    """Reference implementation: enumerate ALL maps ι₂ on [N] and keep those
    that are involutions, preserve every f-orbit, and make f∘ι₂ an involution.
    Exponential — self-test only."""
    from itertools import product
    orbs = []
    seen = set()
    for x in range(N):
        if x not in seen:
            o = orbit_of(f, x)
            seen |= set(o)
            orbs.append(o)
    which = {x: i for i, o in enumerate(orbs) for x in o}
    out = set()
    for vals in product(range(N), repeat=N):
        i2 = dict(enumerate(vals))
        if any(which[x] != which[i2[x]] for x in range(N)):
            continue
        if any(i2[i2[x]] != x for x in range(N)):
            continue
        i1 = {x: f[i2[x]] for x in range(N)}
        if any(i1[i1[x]] != x for x in range(N)):
            continue
        out.add((i2[0],) if not two_point else (i2[0], i2[1]))
    return out


# ----------------------------------------------------------------------
# The minimax game.
# ----------------------------------------------------------------------

class Game:
    def __init__(self, N, n, promise=None, two_point=False, paranoid=False):
        self.N, self.n, self.promise = N, n, promise
        self.two = two_point
        self.paranoid = paranoid
        self.designated = (0, 1) if two_point else (0,)
        self.val_memo = {}
        self.term_memo = {}
        self.deadline = None

    # -- canonicalization -------------------------------------------------
    def canon(self, T, extra_mark=None):
        """Hashable key for T up to relabeling points other than the
        designated ones.  extra_mark tags a node (used to dedupe queries)."""
        def flag(v):
            b = 0
            if v == 0:
                b |= 1
            if self.two and v == 1:
                b |= 2
            if v == extra_mark:
                b |= 4
            return b
        paths, cycles, untouched = components(T, self.N)
        keys = []
        for p in paths:
            keys.append(('p', tuple(flag(v) for v in p)))
        for c in cycles:
            flags = [flag(v) for v in c]
            L = len(c)
            best = min(tuple(flags[(i + r) % L] for i in range(L))
                       for r in range(L))
            keys.append(('c', best))
        ufl = tuple(sorted(flag(v) for v in untouched if flag(v)))
        return (tuple(sorted(keys)), ufl, len(untouched))

    # -- win test ----------------------------------------------------------
    def terminal(self, T):
        key = self.canon(T)
        if key in self.term_memo:
            return self.term_memo[key]
        if not self.two and not self.paranoid:
            # Game A: v = 0 always wins — the m=0 reflection of 0's orbit
            # fixes 0 for EVERY f (lemma verified in self_test).
            res = True
        else:
            inter = None
            for f in completions(dict(T), self.N, self.n, self.promise,
                                 self.deadline):
                vo = valid_outputs(f, self.two)
                inter = vo if inter is None else inter & vo
                if not inter:
                    break
            res = bool(inter)
        self.term_memo[key] = res
        return res

    # -- minimax value -----------------------------------------------------
    def value(self, T):
        if time.monotonic() > self.deadline:
            raise Timeout
        key = self.canon(T)
        if key in self.val_memo:
            return self.val_memo[key]
        if self.terminal(T):
            self.val_memo[key] = 0
            return 0
        has_pred = set(T.values())
        best = self.N  # value ≤ N-1 always (full knowledge ⇒ terminal)
        seen_q = set()
        for x in range(self.N):
            if x in T:
                continue  # f(x) already known: a wasted query, never optimal
            qk = self.canon(T, extra_mark=x)
            if qk in seen_q:
                continue
            seen_q.add(qk)
            worst = 0
            seen_a = set()
            for y in range(self.N):
                if y in has_pred:
                    continue
                T[x] = y
                ok = consistent(T, self.N, self.n, self.promise)
                ak = self.canon(T) if ok else None
                if ok and ak not in seen_a:
                    seen_a.add(ak)
                    worst = max(worst, self.value(dict(T)))
                del T[x]
                if worst + 1 >= best:
                    break  # alpha-beta style cut
            best = min(best, 1 + worst)
        self.val_memo[key] = best
        return best

    def solve(self, time_cap=TIME_CAP):
        self.deadline = time.monotonic() + time_cap
        root = {}
        if not consistent(root, self.N, self.n, self.promise):
            return None  # promise infeasible (e.g. ℓ > N)
        return self.value(root)


# ----------------------------------------------------------------------
# Self tests.
# ----------------------------------------------------------------------

def all_perms_order_dividing(N, n):
    yield from completions({}, N, n, None, time.monotonic() + 3600)


def self_test():
    print("self-test: reflection lemma (valid_outputs vs brute force) ...")
    for N in (3, 4, 5):
        for n in (2, 3, 4, 6):
            cnt = 0
            for f in all_perms_order_dividing(N, n):
                for two in (False, True):
                    a = valid_outputs(f, two)
                    b = valid_outputs_bruteforce(f, N, two)
                    assert a == b, (N, n, f, two, a, b)
                cnt += 1
            print(f"  N={N} n={n}: {cnt} permutations checked")
    print("self-test: Game A terminal-at-root by full enumeration ...")
    for N in (4, 5):
        for n in (2, 3, 4, 6):
            for promise in [None] + [l for l in divisors(n) if l <= N]:
                g = Game(N, n, promise, two_point=False, paranoid=True)
                v = g.solve(60)
                assert v == 0, (N, n, promise, v)
    print("  Game A value 0 confirmed by exhaustive check (N=4,5, all n, all ℓ)")
    print("self-test: consistency filter sanity ...")
    # a 2-path cannot exist when n = 2 forces it into a 2-cycle with promise 1
    assert consistent({0: 1}, 4, 2, None)
    assert not consistent({0: 1}, 4, 2, 1)       # orbit(0) would exceed 1
    assert not consistent({0: 1, 1: 2}, 4, 2, None)  # 3-node path, n=2
    assert consistent({0: 1, 1: 2}, 4, 3, None)
    assert not consistent({0: 1, 1: 0}, 4, 3, None)  # 2-cycle, n=3
    print("all self-tests passed")


# ----------------------------------------------------------------------
# Main experiment.
# ----------------------------------------------------------------------

def fmt(v):
    return "t/o" if v == "t/o" else ("-" if v is None else str(v))


def main():
    args = set(sys.argv[1:])
    if "--selftest" in args:
        self_test()
        return
    paranoid = "--paranoid" in args

    Ns = range(4, 10)
    ns = (2, 3, 4, 6)
    print("Exact minimax query complexity of the orbit-preserving")
    print("two-involution game (adversary constrained by f^n = id).")
    print("A  = single designated point x0=0 (the literal game)")
    print("B  = two designated points 0,1 with one shared ι₂ (global-")
    print("     consistency proxy).  ℓ=* means no orbit-length promise.")
    print()
    header = f"{'N':>2} {'n':>2} {'ℓ':>2} | {'q(A)':>5} {'q(B)':>5}"
    print(header)
    print("-" * len(header))
    for N in Ns:
        for n in ns:
            for promise in [None] + [l for l in divisors(n) if l <= N]:
                row = []
                for two in (False, True):
                    g = Game(N, n, promise, two_point=two, paranoid=paranoid)
                    try:
                        t0 = time.monotonic()
                        v = g.solve()
                        dt = time.monotonic() - t0
                        row.append((v, dt))
                    except Timeout:
                        row.append(("t/o", TIME_CAP))
                (va, ta), (vb, tb) = row
                lp = "*" if promise is None else str(promise)
                print(f"{N:>2} {n:>2} {lp:>2} | {fmt(va):>5} {fmt(vb):>5}"
                      f"   ({ta:.1f}s / {tb:.1f}s)")
        print("-" * len(header))


if __name__ == "__main__":
    main()
