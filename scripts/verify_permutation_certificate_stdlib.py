#!/usr/bin/env python3
"""Stdlib-only checker for #1038 permutation/piecewise-shift certificates."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Iterable, Optional


POLE_EPS = 1.0e-10
UNIQ_EPS = 1.0e-8


def v_value(y: float, ds: list[float], weights: list[float]) -> float:
    return -math.log(abs(y)) - sum(weight * math.log(abs(y - d)) for weight, d in zip(weights, ds))


def v_derivative(y: float, ds: list[float], weights: list[float]) -> float:
    return -(1.0 / y) - sum(weight / (y - d) for weight, d in zip(weights, ds))


def split_interval(lo: float, hi: float, ds: Iterable[float]) -> list[tuple[float, float]]:
    cuts = sorted([lo, hi] + [d for d in ds if lo < d < hi])
    segments: list[tuple[float, float]] = []
    for left, right in zip(cuts[:-1], cuts[1:]):
        safe_left = left + (POLE_EPS if any(abs(left - d) < 1.0e-14 for d in ds) else 0.0)
        safe_right = right - (POLE_EPS if any(abs(right - d) < 1.0e-14 for d in ds) else 0.0)
        if safe_left < safe_right:
            segments.append((safe_left, safe_right))
    return segments


def bisect_root(lo: float, hi: float, ds: list[float], weights: list[float]) -> Optional[float]:
    flo = v_derivative(lo, ds, weights)
    fhi = v_derivative(hi, ds, weights)
    if not (math.isfinite(flo) and math.isfinite(fhi)):
        return None
    if flo == 0.0:
        return lo
    if fhi == 0.0:
        return hi
    if flo * fhi > 0.0:
        return None

    left, right = lo, hi
    fleft = flo
    for _ in range(90):
        mid = 0.5 * (left + right)
        fmid = v_derivative(mid, ds, weights)
        if not math.isfinite(fmid):
            return None
        if fleft * fmid <= 0.0:
            right = mid
        else:
            left = mid
            fleft = fmid
    return 0.5 * (left + right)


def unique_points(points: Iterable[float], ds: list[float]) -> list[float]:
    out: list[float] = []
    for point in sorted(points):
        if any(abs(point - d) <= POLE_EPS for d in ds):
            continue
        if all(abs(point - old) > UNIQ_EPS for old in out):
            out.append(point)
    return out


def min_on_intervals(intervals: list[tuple[float, float]], ds: list[float], weights: list[float]):
    points: list[float] = []
    for lo, hi in intervals:
        points.extend([lo, hi])
        for left, right in split_interval(lo, hi, ds):
            root = bisect_root(left, right, ds, weights)
            if root is not None:
                points.append(root)

    points = unique_points(points, ds)
    values = [(v_value(point, ds, weights), point) for point in points]
    value, argmin = min(values, key=lambda item: item[0])
    return value, argmin, points


def is_permutation(values: list[int], k: int) -> bool:
    return sorted(values) == list(range(k))


def permutation_runs(values: list[int]) -> list[dict]:
    runs = []
    start = None
    prev = None
    for i, value in enumerate(values):
        if value != i:
            if start is None:
                start = i
            prev = i
        elif start is not None:
            runs.append({"i0": start, "i1": prev, "slot0": values[start], "slot1": values[prev]})
            start = None
    if start is not None:
        runs.append({"i0": start, "i1": prev, "slot0": values[start], "slot1": values[prev]})
    return runs


def verify(cert: dict) -> dict:
    m_value = float(cert["M"])
    base = float(cert["base"])
    k_blocks = int(cert["K"])
    h = float(cert.get("h", (m_value - base) / k_blocks))
    starts = [float(x) for x in cert["lane_starts_s"]]
    permutations = [[int(x) for x in lane] for lane in cert["permutations"]]

    permutation_summary = []
    for lane, perm in enumerate(permutations):
        permutation_summary.append(
            {
                "lane": lane,
                "length": len(perm),
                "is_permutation": is_permutation(perm, k_blocks),
                "nonidentity_count": sum(1 for i, slot in enumerate(perm) if i != slot),
                "nonidentity_runs": permutation_runs(perm),
            }
        )

    rows = []
    bad = []
    stored_diffs = []
    for i, weights_raw in enumerate(cert["weights"]):
        A = m_value - i * h
        C = A - h
        T0, T1 = min(A, C), max(A, C)
        weights = [float(x) for x in weights_raw]
        ds = [A + starts[j] + permutations[j][i] * h for j in range(len(starts))]
        intervals = [(T0 - 1.0, T1 - 1.0), (T0, T1 + 1.0)]
        margin, argmin, points = min_on_intervals(intervals, ds, weights)
        stored_margin = float(cert["margins"][i]) if "margins" in cert else math.nan
        stored_y = float(cert["y_min"][i]) if "y_min" in cert else math.nan
        row = {
            "i": i,
            "A": A,
            "C": C,
            "required_margin": margin,
            "required_argmin_y": argmin,
            "stored_margin": stored_margin,
            "stored_argmin_y": stored_y,
            "abs_margin_diff": abs(margin - stored_margin) if math.isfinite(stored_margin) else math.nan,
            "abs_argmin_y_diff": abs(argmin - stored_y) if math.isfinite(stored_y) else math.nan,
            "num_check_points": len(points),
        }
        for j, d in enumerate(ds):
            row[f"d{j}"] = d
            row[f"w{j}"] = weights[j]
            row[f"pi{j}"] = permutations[j][i]
        rows.append(row)
        if margin <= 0.0:
            bad.append(row)
        if math.isfinite(stored_margin):
            stored_diffs.append(abs(margin - stored_margin))

    margins = sorted(row["required_margin"] for row in rows)
    worst = min(rows, key=lambda row: row["required_margin"])
    max_margin_diff = max(stored_diffs) if stored_diffs else math.nan
    summary = {
        "input_problem": cert.get("problem"),
        "input_status": cert.get("status"),
        "M": m_value,
        "base": base,
        "K": k_blocks,
        "h": h,
        "lane_starts_s": starts,
        "permutation_summary": permutation_summary,
        "all_lanes_are_permutations": all(item["is_permutation"] for item in permutation_summary),
        "num_blocks": len(rows),
        "bad_required_blocks": len(bad),
        "all_required_blocks_ok": len(bad) == 0,
        "worst_required": {
            "block": worst["i"],
            "value": worst["required_margin"],
            "argmin_y": worst["required_argmin_y"],
        },
        "stored_worst": {
            "block": cert.get("worst_block"),
            "value": cert.get("worst_margin"),
        },
        "max_abs_margin_diff_from_stored": max_margin_diff,
        "margin_quantiles": {
            "min": margins[0],
            "q05": margins[int(0.05 * (len(margins) - 1))],
            "median": margins[len(margins) // 2],
            "q95": margins[int(0.95 * (len(margins) - 1))],
            "max": margins[-1],
        },
        "top_12_tight_blocks": [
            {
                "block": row["i"],
                "required_margin": row["required_margin"],
                "required_argmin_y": row["required_argmin_y"],
                "pi": [row[f"pi{j}"] for j in range(len(starts))],
            }
            for row in sorted(rows, key=lambda item: item["required_margin"])[:12]
        ],
    }
    return {"summary": summary, "rows": rows}


def write_csv(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--out-json", type=Path)
    parser.add_argument("--out-csv", type=Path)
    args = parser.parse_args()

    cert = json.loads(args.input.read_text())
    result = verify(cert)
    if args.out_json:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(result["summary"], indent=2) + "\n")
    if args.out_csv:
        write_csv(args.out_csv, result["rows"])
    print(json.dumps(result["summary"], indent=2))
    return 0 if result["summary"]["all_required_blocks_ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
