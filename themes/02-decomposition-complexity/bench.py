#!/usr/bin/env python3
"""二対合分解 f = i1 . i2 のコスト実測.

finite_order.decompose を計装し、i1/i2 の 1 評価あたりに f が
何回呼ばれるかを位数 n を変えて数える。仮説: O(n)。
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from finite_order import decompose  # noqa: E402


def cyclic(n: int, blocks: int = 50):
    """位数 n の全単射: ブロックごとの n-サイクル (x -> x+1 mod n)."""
    def f(x: int) -> int:
        b, r = divmod(x, n)
        return b * n + (r + 1) % n if b < blocks else x
    return f


def count_calls(n: int, sample: range) -> float:
    calls = 0
    f = cyclic(n)

    def counted(x: int) -> int:
        nonlocal calls
        calls += 1
        return f(x)

    i1, i2 = decompose(counted, n)
    calls = 0
    for x in sample:
        i2(x)
        i1(x)
    evals = 2 * len(sample)
    return calls / evals


def main() -> None:
    print(f"{'order n':>8} {'f-calls per i-eval':>20}")
    for n in [2, 3, 5, 8, 13, 21, 34, 55]:
        avg = count_calls(n, range(0, n * 20))
        print(f"{n:>8} {avg:>20.1f}")
    print("\n仮説: 呼び出し回数は n に比例する（軌道走査コスト）。")
    print("次の一歩: この上界を証明し、オラクル下界 Ω(n) を検討する。")


if __name__ == "__main__":
    main()
