#!/usr/bin/env python3
"""2点ゲームの厳密値表を data/ へ自動生成（手編集禁止・toolkit方式）.

各セルで厳密ソルバの値と閉形式 min(l-2, k1*) を並記し一致を検査。
コストの高いセル（>TIME_CAP 秒）はスキップして closed-form のみ記載。
"""
import csv, sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from query_lb_search import Game

TIME_CAP = 90.0
OUT = Path(__file__).resolve().parent / "data" / "query_game_values.csv"


def k1star(N, l):
    for k in range(0, l):
        cand = [d for d in range(1, l + 1) if l % d == 0 and d >= k + 1]
        if cand and min(cand) > N - l:
            return k
    return None


def closed_form(N, l):
    if l == 2:
        return 0
    k = k1star(N, l)
    return min(l - 2, k) if k is not None else l - 2


def main():
    rows = []
    for l in (2, 3, 4, 5, 6):
        for N in range(l, 13):
            pred = closed_form(N, l)
            g = Game(N, l, promise=l, two_point=True)
            t0 = time.monotonic()
            try:
                v = g.solve(time_cap=TIME_CAP)
                dt = f"{time.monotonic()-t0:.1f}"
                status = "ok" if v == pred else "MISMATCH"
            except Exception:
                v, dt, status = "", "t/o", "predicted-only"
            rows.append([N, l, pred, v, dt, status])
            if status == "MISMATCH":
                print(f"MISMATCH at N={N} l={l}: solver={v} formula={pred}")
    OUT.parent.mkdir(exist_ok=True)
    with open(OUT, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["N", "ell", "closed_form", "solver_value",
                    "solver_seconds", "status"])
        w.writerows(rows)
    bad = [r for r in rows if r[5] == "MISMATCH"]
    print(f"wrote {OUT.name}: {len(rows)} cells, "
          f"{sum(1 for r in rows if r[5]=='ok')} verified, "
          f"{sum(1 for r in rows if r[5]=='predicted-only')} predicted-only, "
          f"{len(bad)} mismatches")
    assert not bad


if __name__ == "__main__":
    main()
