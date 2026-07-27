#!/usr/bin/env python3
"""鏡映複製（doubling）構成の等式検証（research/11 の定理 11.1）.

ρ̂(x,0) = (ρ₀(x),0), ρ̂(x,1) = (ρ₀⁻¹(x),1), ι(x,i) = (x,1−i) について
  ι² = id,  ι ρ̂ ι = ρ̂⁻¹
を、有限モデル（Z 鎖の代わりに大きな巡回で近似した ρ₀ と、
複数チェーンを持つ ρ₀）でサンプル検査する。
"""
M = 997  # 「無限鎖」の有限近似（十分大きい巡回）


def rho0(x):          # 複数チェーン: ブロック b ごとに +1 巡回
    b, r = divmod(x, M)
    return b * M + (r + 1) % M


def rho0_inv(x):
    b, r = divmod(x, M)
    return b * M + (r - 1) % M


def rho_hat(p):
    x, i = p
    return (rho0(x), 0) if i == 0 else (rho0_inv(x), 1)


def rho_hat_inv(p):
    x, i = p
    return (rho0_inv(x), 0) if i == 0 else (rho0(x), 1)


def iota(p):
    x, i = p
    return (x, 1 - i)


def main():
    pts = [(x, i) for x in range(5 * M) for i in (0, 1)]
    for p in pts:
        assert iota(iota(p)) == p
        assert iota(rho_hat(iota(p))) == rho_hat_inv(p)
        assert rho_hat(rho_hat_inv(p)) == p
    # ι は鎖を必ず「相方の鏡像鎖」へ写す（固定鎖ゼロ）: 定理7.2 と整合
    for p in pts[:2 * M]:
        x, i = p
        assert iota(p)[1] != i
    print(f"doubling check: OK on {len(pts)} points "
          "(iota^2=id, iota rho iota = rho^{-1}, no fixed chains)")


if __name__ == "__main__":
    main()
