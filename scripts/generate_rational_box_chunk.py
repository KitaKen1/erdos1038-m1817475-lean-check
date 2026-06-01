#!/usr/bin/env python3
"""Generate Lean rational-box chunks for the #1038 permutation certificate.

The generator is intentionally outside Lean.  The generated file is checked by
Lean using exact rational arithmetic.  If the boxes fail to cover the required
interval or any rational lower bound is non-positive, Lean rejects the theorem.
"""

from __future__ import annotations

import argparse
import json
import math
from decimal import Decimal
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CERT = ROOT / "certificates" / "ehp1038_M1817475_v2_experimental_certificate.json"
DEFAULT_OUT = ROOT / "Erdos1038Lean" / "M1817475"


def frac_from_decimal(value) -> Fraction:
    if isinstance(value, Decimal):
        return Fraction(value)
    return Fraction(Decimal(str(value)))


def rat(x: Fraction) -> str:
    if x.denominator == 1:
        return f"({x.numerator} : Rat)"
    return f"(({x.numerator} : Rat) / {x.denominator})"


def atanh_lower(t: float, n: int) -> float:
    total = 0.0
    power = t
    t2 = t * t
    for k in range(n):
        total += power / (2 * k + 1)
        power *= t2
    return 2.0 * total


def atanh_upper(t: float, n: int) -> float:
    power = t ** (2 * n + 1)
    return atanh_lower(t, n) + 2.0 * power / (1.0 - t * t)


def log_inv_lower_float(d: float, npos: int, nneg: int) -> float:
    if d < 1.0:
        return atanh_lower((1.0 - d) / (1.0 + d), npos)
    return -atanh_upper((d - 1.0) / (d + 1.0), nneg)


def atanh_lower_fraction(t: Fraction, n: int) -> Fraction:
    total = Fraction(0)
    power = t
    t2 = t * t
    for k in range(n):
        total += power / (2 * k + 1)
        power *= t2
    return 2 * total


def atanh_upper_fraction(t: Fraction, n: int) -> Fraction:
    return atanh_lower_fraction(t, n) + 2 * t ** (2 * n + 1) / (1 - t * t)


def log_inv_lower_fraction(d: Fraction, npos: int, nneg: int) -> Fraction:
    if d < 1:
        return atanh_lower_fraction((1 - d) / (1 + d), npos)
    return -atanh_upper_fraction((d - 1) / (d + 1), nneg)


def weighted_lower_fraction(distances: list[Fraction], weights: list[Fraction], npos: int, nneg: int) -> Fraction:
    total = log_inv_lower_fraction(distances[0], npos, nneg)
    for weight, distance in zip(weights, distances[1:]):
        total += weight * log_inv_lower_fraction(distance, npos, nneg)
    return total


def approx_lower(lo: Fraction, hi: Fraction, weights: list[Fraction], shifts: list[Fraction], npos: int, nneg: int) -> float:
    ds = [max(abs(float(lo)), abs(float(hi)))]
    ds += [max(abs(float(lo - s)), abs(float(hi - s))) for s in shifts]
    total = log_inv_lower_float(ds[0], npos, nneg)
    for w, d in zip(weights, ds[1:]):
        total += float(w) * log_inv_lower_float(d, npos, nneg)
    return total


def split_at_poles(intervals: list[tuple[Fraction, Fraction]], shifts: list[Fraction]) -> list[tuple[Fraction, Fraction]]:
    out: list[tuple[Fraction, Fraction]] = []
    for lo, hi in intervals:
        pts = sorted(set([lo, hi] + [s for s in shifts if lo < s < hi]))
        for left, right in zip(pts, pts[1:]):
            if left < right:
                out.append((left, right))
    return out


def cover(lo: Fraction, hi: Fraction, weights: list[Fraction], shifts: list[Fraction], threshold: float, depth: int, max_depth: int, npos: int, nneg: int):
    if approx_lower(lo, hi, weights, shifts, npos, nneg) > threshold:
        return [(lo, hi)]
    if depth >= max_depth:
        raise RuntimeError({
            "lo": float(lo),
            "hi": float(hi),
            "approx_lower": approx_lower(lo, hi, weights, shifts, npos, nneg),
        })
    mid = (lo + hi) / 2
    return (
        cover(lo, mid, weights, shifts, threshold, depth + 1, max_depth, npos, nneg)
        + cover(mid, hi, weights, shifts, threshold, depth + 1, max_depth, npos, nneg)
    )


def boxes_for_interval(
    lo: Fraction,
    hi: Fraction,
    weights: list[Fraction],
    shifts: list[Fraction],
    threshold: float,
    max_depth: int,
    npos: int,
    nneg: int,
    lb_mode: str,
):
    out = []
    for left, right in split_at_poles([(lo, hi)], shifts):
        for L, R in cover(left, right, weights, shifts, threshold, 0, max_depth, npos, nneg):
            distances = [max(abs(L), abs(R))]
            distances += [max(abs(L - s), abs(R - s)) for s in shifts]
            if lb_mode == "exact":
                lower_bound = weighted_lower_fraction(distances, weights, npos, nneg)
            else:
                lower_bound = Fraction(Decimal(str(approx_lower(L, R, weights, shifts, npos, nneg))))
            out.append((weights, shifts, L, R, distances, lower_bound))
    return out


def box_line(item) -> str:
    weights, shifts, L, R, distances, lower_bound = item
    fields = [
        ("w1", weights[0]), ("w2", weights[1]), ("w3", weights[2]), ("w4", weights[3]),
        ("s1", shifts[0]), ("s2", shifts[1]), ("s3", shifts[2]), ("s4", shifts[3]),
        ("L", L), ("R", R),
        ("D0", distances[0]), ("D1", distances[1]), ("D2", distances[2]), ("D3", distances[3]), ("D4", distances[4]),
        ("LB", lower_bound),
    ]
    return "  { " + ", ".join(f"{name} := {rat(value)}" for name, value in fields) + " }"


def lean_list(name: str, boxes) -> str:
    if not boxes:
        return f"def {name} : List RatBox := []"
    return f"def {name} : List RatBox := [\n" + ",\n".join(box_line(box) for box in boxes) + "\n]"


def chunks(items, size: int):
    for start in range(0, len(items), size):
        yield start // size, items[start:start + size]


def generate_block(cert: dict, i: int, threshold: float, max_depth: int, npos: int, nneg: int, lb_mode: str) -> tuple[str, dict]:
    m_value = frac_from_decimal(cert["M"])
    base = frac_from_decimal(cert["base"])
    k_blocks = int(cert["K"])
    h = frac_from_decimal(cert.get("h", Fraction(m_value - base, k_blocks)))
    starts = [frac_from_decimal(x) for x in cert["lane_starts_s"]]
    permutations = [[int(x) for x in lane] for lane in cert["permutations"]]

    A = m_value - i * h
    C = A - h
    weights = [frac_from_decimal(x) for x in cert["weights"][i]]
    shifts = [A + starts[j] + permutations[j][i] * h for j in range(4)]
    leftL, leftR = C - 1, A - 1
    rightL, rightR = C, A + 1
    left_boxes = boxes_for_interval(leftL, leftR, weights, shifts, threshold, max_depth, npos, nneg, lb_mode)
    right_boxes = boxes_for_interval(rightL, rightR, weights, shifts, threshold, max_depth, npos, nneg, lb_mode)

    module = f"Block{i:03d}" if i != 196 else "Block196"
    ns = f"block{i:03d}" if i != 196 else "block196"
    chunk_size = 100
    right_chunks = list(chunks(right_boxes, chunk_size))

    def chunk_left(chunk):
        return chunk[0][2]

    def chunk_right(chunk):
        return chunk[-1][3]

    lines = [
        "import Erdos1038Lean.RationalKernel",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 100000",
        "",
        "namespace Erdos1038Lean",
        "namespace M1817475",
        f"namespace {module}",
        "",
        f"def {ns}LeftL : Rat := {rat(leftL)}",
        f"def {ns}LeftR : Rat := {rat(leftR)}",
        f"def {ns}RightL : Rat := {rat(rightL)}",
        f"def {ns}RightR : Rat := {rat(rightR)}",
        "",
        lean_list(f"{ns}LeftBoxes", left_boxes),
        "",
        f"def {ns}LeftCertificate : Bool :=",
            f"  allBoxesValid {ns}LeftBoxes &&",
        f"  coversFromBool {ns}LeftBoxes {ns}LeftL {ns}LeftR",
        "",
        f"theorem {ns}LeftCertificate_eq_true :",
        f"    {ns}LeftCertificate = true := by",
        "  native_decide",
        "",
    ]

    chain_terms = []
    right_cert_names = []
    for idx, chunk in right_chunks:
        cname = f"{ns}RightChunk{idx:03d}"
        cert_name = f"{cname}Certificate"
        right_cert_names.append(cert_name)
        cL = chunk_left(chunk)
        cR = chunk_right(chunk)
        if idx == 0:
            chain_terms.append(f"{ns}RightL = {rat(cL)}")
        else:
            prev = right_chunks[idx - 1][1]
            chain_terms.append(f"{rat(chunk_right(prev))} = {rat(cL)}")
        lines += [
            lean_list(cname, chunk),
            "",
            f"def {cname}L : Rat := {rat(cL)}",
            f"def {cname}R : Rat := {rat(cR)}",
            "",
            f"def {cert_name} : Bool :=",
            f"  allBoxesValid {cname} &&",
            f"  coversFromBool {cname} {cname}L {cname}R",
            "",
            f"theorem {cert_name}_eq_true :",
            f"    {cert_name} = true := by",
            "  native_decide",
            "",
        ]
    if right_chunks:
        chain_terms.append(f"{rat(chunk_right(right_chunks[-1][1]))} = {ns}RightR")
    chain_prop = " /\\\n    ".join(chain_terms) if chain_terms else "True"
    lines += [
        f"def {ns}RightChainCertificate : Bool :=",
        f"  decide (",
        f"    {chain_prop})",
        "",
        f"theorem {ns}RightChainCertificate_eq_true :",
        f"    {ns}RightChainCertificate = true := by",
        "  native_decide",
        "",
    ]
    cert_props = [f"{ns}LeftCertificate = true", f"{ns}RightChainCertificate = true"]
    cert_props += [f"{name} = true" for name in right_cert_names]
    cert_prop_text = " /\\\n    ".join(cert_props)
    proof_terms = [f"{ns}LeftCertificate_eq_true", f"{ns}RightChainCertificate_eq_true"]
    proof_terms += [f"{name}_eq_true" for name in right_cert_names]
    exact_tuple = "⟨" + ", ".join(proof_terms) + "⟩"
    lines += [
        f"def {ns}LeftBoxCount : Nat := boxCount {ns}LeftBoxes",
        f"def {ns}RightBoxCount : Nat := {len(right_boxes)}",
        "",
        f"def {ns}_rational_certificate : Prop :=",
        f"    {cert_prop_text}",
        "",
        f"theorem {ns}_rational_certificate_proof :",
        f"    {ns}_rational_certificate := by",
        f"  exact {exact_tuple}",
        "",
        f"end {module}",
        "end M1817475",
        "end Erdos1038Lean",
        "",
    ]
    meta = {
        "block": i,
        "left_boxes": len(left_boxes),
        "right_boxes": len(right_boxes),
        "A": str(A),
        "C": str(C),
        "left_domain": [str(leftL), str(leftR)],
        "right_domain": [str(rightL), str(rightR)],
        "shifts": [str(x) for x in shifts],
        "weights": [str(x) for x in weights],
        "lower_bound_mode": lb_mode,
        "note": (
            "float mode stores externally computed lower-bound rationals for Lean to check positive; "
            "exact mode recomputes atanh lower bounds as Fractions during generation."
        ),
    }
    return "\n".join(lines), meta


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_CERT)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--block", type=int, default=196)
    parser.add_argument("--threshold", type=float, default=1e-7)
    parser.add_argument("--max-depth", type=int, default=32)
    parser.add_argument("--npos", type=int, default=150)
    parser.add_argument("--nneg", type=int, default=150)
    parser.add_argument("--lb-mode", choices=["float", "exact"], default="float")
    args = parser.parse_args()

    cert = json.loads(args.input.read_text(), parse_float=Decimal)
    text, meta = generate_block(cert, args.block, args.threshold, args.max_depth, args.npos, args.nneg, args.lb_mode)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    module_name = "Block196" if args.block == 196 else f"Block{args.block:03d}"
    (args.out_dir / f"{module_name}.lean").write_text(text)
    (args.out_dir / f"{module_name}.json").write_text(json.dumps(meta, indent=2))
    print(json.dumps(meta, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
