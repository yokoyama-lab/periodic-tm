#!/usr/bin/env python3
"""2 点ゲームの厳密値を N <= NMAX の**全セル**（2 <= ℓ <= N）で測り直す（2026-10-11 追加）。

`gen_value_table.py` は ℓ <= 6 の 45 セルだけを回し、1 セル 90 秒で打ち切る
（(12,4)・(12,5)・(12,6) が t/o → predicted-only）。原稿 note.tex §6 の
「every instance with N <= 12」はこの表を指していたが、ℓ = 7..12 の 21 セルは
1 つも測っておらず、ℓ <= 6 でも 3 セルが未測定だった（査読 2026-09-18 の必須 3）。

このスクリプトは:

* 各セルを**別プロセス**で解く（メモリをセルごとに返す。OOM で死んでも他のセルは残る）
* 打ち切りは `query_lb_search.Timeout` だけを t/o と読む。それ以外の例外・異常終了は
  `error` / `killed(rc)` として残し、**値とも打ち切りとも読まない**
* 1 セル終わるごとに jsonl に追記する（途中で止まっても結果が残る）
* 最後に CSV（`data/query_game_values_full.csv`）を書き、閉形式 min(ℓ-2, k1*) と照合する

使い方:
    python3 value_table_full.py --nmax 12 --cap 72000 --jobs 8
    python3 value_table_full.py --cell 12 6 --cap 600   # 1 セルだけ（子プロセス用）
"""
import argparse
import csv
import json
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))


def solve_cell(N, l, cap):
    import resource
    from query_lb_search import Game, Timeout
    from gen_value_table import closed_form
    pred = closed_form(N, l)
    g = Game(N, l, promise=l, two_point=True)
    t0 = time.monotonic()
    try:
        v = g.solve(time_cap=cap)
        status = "ok" if v == pred else "MISMATCH"
    except Timeout:
        v, status = None, "t/o"
    dt = time.monotonic() - t0
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss  # KB
    return {"N": N, "ell": l, "closed_form": pred, "solver_value": v,
            "solver_seconds": round(dt, 1), "status": status,
            "cap": cap, "maxrss_mb": round(rss / 1024, 1),
            "val_memo": len(g.val_memo), "term_memo": len(g.term_memo)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=12)
    ap.add_argument("--cap", type=float, default=72000.0, help="1 セルの秒数上限")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--out", default=str(HERE / "data" / "query_game_values_full.csv"))
    ap.add_argument("--log", default=None, help="jsonl（既定: --out の拡張子を .jsonl に）")
    ap.add_argument("--cell", nargs=2, type=int, metavar=("N", "ELL"))
    a = ap.parse_args()

    if a.cell:
        print(json.dumps(solve_cell(a.cell[0], a.cell[1], a.cap)), flush=True)
        return 0

    log = Path(a.log or Path(a.out).with_suffix(".jsonl"))
    done = {}
    if log.exists():
        for ln in log.read_text().splitlines():
            r = json.loads(ln)
            if r["status"] in ("ok", "MISMATCH"):
                done[(r["N"], r["ell"])] = r
    cells = [(N, l) for N in range(2, a.nmax + 1) for l in range(2, N + 1)]
    todo = [c for c in cells if c not in done]
    todo.sort(key=lambda c: (-c[0], c[1]))  # 重い（N が大きい）セルから
    print(f"cells={len(cells)} done={len(done)} todo={len(todo)} cap={a.cap}s jobs={a.jobs}",
          flush=True)

    running = {}
    while todo or running:
        while todo and len(running) < a.jobs:
            N, l = todo.pop(0)
            p = subprocess.Popen([sys.executable, "-B", __file__, "--cell", str(N), str(l),
                                  "--cap", str(a.cap)],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            running[p] = (N, l, time.monotonic())
        time.sleep(1.0)
        for p in [p for p in running if p.poll() is not None]:
            N, l, t0 = running.pop(p)
            out, err = p.communicate()
            if p.returncode == 0 and out.strip():
                r = json.loads(out.strip().splitlines()[-1])
            else:
                r = {"N": N, "ell": l, "solver_value": None,
                     "solver_seconds": round(time.monotonic() - t0, 1),
                     "status": f"killed(rc={p.returncode})" if p.returncode < 0 or p.returncode in (137, 143)
                     else f"error(rc={p.returncode})",
                     "stderr_tail": err[-400:]}
                from gen_value_table import closed_form
                r["closed_form"] = closed_form(N, l)
            with log.open("a") as f:
                f.write(json.dumps(r) + "\n")
            done[(N, l)] = r
            print(f"N={N} l={l}: {r['status']} v={r['solver_value']} "
                  f"pred={r['closed_form']} {r['solver_seconds']}s", flush=True)

    rows = [done[c] for c in sorted(done, key=lambda c: (c[1], c[0]))]
    with open(a.out, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["N", "ell", "closed_form", "solver_value", "solver_seconds", "status"])
        for r in rows:
            w.writerow([r["N"], r["ell"], r["closed_form"],
                        "" if r["solver_value"] is None else r["solver_value"],
                        r["solver_seconds"], r["status"]])
    ok = sum(r["status"] == "ok" for r in rows)
    bad = [r for r in rows if r["status"] == "MISMATCH"]
    other = [r for r in rows if r["status"] not in ("ok", "MISMATCH")]
    print(f"wrote {a.out}: {len(rows)} cells, {ok} verified, {len(bad)} mismatches, "
          f"{len(other)} not measured ({', '.join(f'({r['N']},{r['ell']}) {r['status']}' for r in other)})")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
