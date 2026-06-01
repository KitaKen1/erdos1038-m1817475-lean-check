#!/usr/bin/env python3
"""High-precision Decimal checker for #1038 permutation certificates.

This is still not a formal proof: Decimal elementary functions are not a proof
assistant and do not provide theorem-level outward rounding.  It is, however, a
useful independent hardening step beyond double precision.
"""

from __future__ import annotations

import argparse
import csv
import json
from decimal import Decimal, localcontext
from pathlib import Path
from typing import Iterable, Optional


def dabs(x: Decimal) -> Decimal:
    return -x if x < 0 else x


def parse_decimal_json(path: Path) -> dict:
    return json.loads(path.read_text(), parse_float=Decimal, parse_int=int)


def v_value(y: Decimal, ds: list[Decimal], weights: list[Decimal]) -> Decimal:
    total = -(dabs(y).ln())
    for weight, shift in zip(weights, ds):
        total -= weight * dabs(y - shift).ln()
    return total


def v_derivative(y: Decimal, ds: list[Decimal], weights: list[Decimal]) -> Decimal:
    total = -(Decimal(1) / y)
    for weight, shift in zip(weights, ds):
        total -= weight / (y - shift)
    return total


def split_interval(lo: Decimal, hi: Decimal, ds: Iterable[Decimal], pole_eps: Decimal) -> list[tuple[Decimal, Decimal]]:
    cuts = sorted([lo, hi] + [shift for shift in ds if lo < shift < hi])
    segments: list[tuple[Decimal, Decimal]] = []
    for left, right in zip(cuts[:-1], cuts[1:]):
        safe_left = left + pole_eps if any(dabs(left - shift) <= pole_eps for shift in ds) else left
        safe_right = right - pole_eps if any(dabs(right - shift) <= pole_eps for shift in ds) else right
        if safe_left < safe_right:
            segments.append((safe_left, safe_right))
    return segments


def bisect_root(
    lo: Decimal,
    hi: Decimal,
    ds: list[Decimal],
    weights: list[Decimal],
    iterations: int,
) -> Optional[Decimal]:
    flo = v_derivative(lo, ds, weights)
    fhi = v_derivative(hi, ds, weights)
    if flo == 0:
        return lo
    if fhi == 0:
        return hi
    if flo * fhi > 0:
        return None

    left, right = lo, hi
    fleft = flo
    two = Decimal(2)
    for _ in range(iterations):
        mid = (left + right) / two
        fmid = v_derivative(mid, ds, weights)
        if fleft * fmid <= 0:
            right = mid
        else:
            left = mid
            fleft = fmid
    return (left + right) / two


def unique_points(points: Iterable[Decimal], ds: list[Decimal], uniq_eps: Decimal, pole_eps: Decimal) -> list[Decimal]:
    out: list[Decimal] = []
    for point in sorted(points):
        if any(dabs(point - shift) <= pole_eps for shift in ds):
            continue
        if all(dabs(point - old) > uniq_eps for old in out):
            out.append(point)
    return out


def min_on_intervals(
    intervals: list[tuple[Decimal, Decimal]],
    ds: list[Decimal],
    weights: list[Decimal],
    pole_eps: Decimal,
    uniq_eps: Decimal,
    iterations: int,
) -> tuple[Decimal, Decimal, int]:
    points: list[Decimal] = []
    for lo, hi in intervals:
        points.extend([lo, hi])
        for left, right in split_interval(lo, hi, ds, pole_eps):
            root = bisect_root(left, right, ds, weights, iterations)
            if root is not None:
                points.append(root)

    points = unique_points(points, ds, uniq_eps, pole_eps)
    vals = [(v_value(point, ds, weights), point) for point in points]
    value, argmin = min(vals, key=lambda item: item[0])
    return value, argmin, len(points)


def quantile(sorted_values: list[Decimal], q: str) -> Decimal:
    qd = Decimal(q)
    idx = int(qd * Decimal(len(sorted_values) - 1))
    return sorted_values[idx]


def verify(cert: dict, precision: int, iterations: int, pole_eps: Decimal, uniq_eps: Decimal) -> dict:
    with localcontext() as ctx:
        ctx.prec = precision
        m_value = Decimal(cert["M"])
        base = Decimal(cert["base"])
        k_blocks = int(cert["K"])
        h = Decimal(cert.get("h", (m_value - base) / Decimal(k_blocks)))
        starts = [Decimal(x) for x in cert["lane_starts_s"]]
        permutations = [[int(x) for x in lane] for lane in cert["permutations"]]

        rows = []
        bad = []
        for i, raw_weights in enumerate(cert["weights"]):
            A = m_value - Decimal(i) * h
            C = A - h
            weights = [Decimal(x) for x in raw_weights]
            ds = [A + starts[j] + Decimal(permutations[j][i]) * h for j in range(len(starts))]
            intervals = [(C - 1, A - 1), (C, A + 1)]
            margin, argmin, point_count = min_on_intervals(intervals, ds, weights, pole_eps, uniq_eps, iterations)
            row = {
                "i": i,
                "required_margin": margin,
                "required_argmin_y": argmin,
                "num_check_points": point_count,
                "stored_margin": Decimal(cert["margins"][i]) if "margins" in cert else None,
            }
            rows.append(row)
            if margin <= 0:
                bad.append(row)

        margins = sorted(row["required_margin"] for row in rows)
        worst = min(rows, key=lambda row: row["required_margin"])
        diffs = [
            dabs(row["required_margin"] - row["stored_margin"])
            for row in rows
            if row["stored_margin"] is not None
        ]
        summary = {
            "mode": "Decimal high precision critical-point checker",
            "precision": precision,
            "root_bisection_iterations": iterations,
            "M": str(m_value),
            "base": str(base),
            "K": k_blocks,
            "h": str(h),
            "bad_required_blocks": len(bad),
            "all_required_blocks_ok": len(bad) == 0,
            "worst_required": {
                "block": worst["i"],
                "value": str(worst["required_margin"]),
                "argmin_y": str(worst["required_argmin_y"]),
            },
            "max_abs_margin_diff_from_stored": str(max(diffs)) if diffs else None,
            "margin_quantiles": {
                "min": str(margins[0]),
                "q05": str(quantile(margins, "0.05")),
                "median": str(margins[len(margins) // 2]),
                "q95": str(quantile(margins, "0.95")),
                "max": str(margins[-1]),
            },
            "top_12_tight_blocks": [
                {
                    "block": row["i"],
                    "required_margin": str(row["required_margin"]),
                    "required_argmin_y": str(row["required_argmin_y"]),
                    "stored_margin": str(row["stored_margin"]) if row["stored_margin"] is not None else None,
                }
                for row in sorted(rows, key=lambda item: item["required_margin"])[:12]
            ],
            "caveat": (
                "High-precision numerical verification only; not interval-certified "
                "and not a formal Lean proof."
            ),
        }
        return {"summary": summary, "rows": rows}


def write_csv(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        fieldnames = ["i", "required_margin", "required_argmin_y", "num_check_points", "stored_margin"]
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({key: str(row[key]) for key in fieldnames})


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--precision", type=int, default=80)
    parser.add_argument("--iterations", type=int, default=180)
    parser.add_argument("--out-json", type=Path)
    parser.add_argument("--out-csv", type=Path)
    args = parser.parse_args()

    cert = parse_decimal_json(args.input)
    result = verify(
        cert,
        precision=args.precision,
        iterations=args.iterations,
        pole_eps=Decimal("1e-40"),
        uniq_eps=Decimal("1e-40"),
    )

    if args.out_json:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(result["summary"], indent=2) + "\n")
    if args.out_csv:
        write_csv(args.out_csv, result["rows"])
    print(json.dumps(result["summary"], indent=2))
    return 0 if result["summary"]["all_required_blocks_ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
