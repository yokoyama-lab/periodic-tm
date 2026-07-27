#!/usr/bin/env python3
"""定理 13.1（半シフト補正）の機械検査.

(1) 整数恒等式 -ceil(t/2) + ceil(-t/2) = -t
(2) シフト付き鏡映対のトイモデルで ι(x) = g(f^{s}(x)) が
    対合的 reverser になること
"""
import math

for t in range(-50, 51):
    assert -math.ceil(t / 2) + math.ceil(-t / 2) == -t

T = {0: 4, 1: -3, 2: 0}          # ペアごとの g^2 シフト t(C)

def f(p):
    k, pid, side = p
    return (k + 1, pid, side)

def f_inv(p):
    k, pid, side = p
    return (k - 1, pid, side)

def g(p):
    k, pid, side = p
    t = T[pid]
    return (-k, pid, 1) if side == 0 else (-k + t, pid, 0)

def iota(p):
    k, pid, side = p
    t = T[pid] if side == 0 else -T[pid]
    s = -math.ceil(t / 2)
    return g((k + s, pid, side))

pts = [(k, pid, s) for k in range(-30, 30) for pid in T for s in (0, 1)]
for p in pts:
    assert g(f(p)) == f_inv(g(p))
for p in pts:
    if abs(p[0]) < 20:
        assert iota(iota(p)) == p
        assert iota(f(p)) == f_inv(iota(p))
print("Theorem 13.1 check: OK (identity + toy model, iota involutive reverser)")
