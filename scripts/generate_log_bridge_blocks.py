#!/usr/bin/env python3
"""Generate Mathlib log-bridge wrappers for all block files.

The generated `BlockNNNLogBridge.lean` files turn the checked rational box
certificates into block-level `ratPotential ... y > 0` theorems, away from the
singular atom locations.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from decimal import Decimal
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DIR = ROOT / "Erdos1038Lean" / "M1817475"
DEFAULT_CERT = ROOT / "certificates" / "ehp1038_M1817475_v2_experimental_certificate.json"


def module_name(i: int) -> str:
    return "Block196" if i == 196 else f"Block{i:03d}"


def ns_name(i: int) -> str:
    return "block196" if i == 196 else f"block{i:03d}"


def rat_from_string(text: str) -> Fraction:
    return Fraction(text)


def rat(x: Fraction) -> str:
    if x.denominator == 1:
        return f"({x.numerator} : Rat)"
    return f"(({x.numerator} : Rat) / {x.denominator})"


def theorem_name(ns: str, suffix: str) -> str:
    return f"{ns}_{suffix}"


def exclusions(ns: str) -> list[str]:
    return [
        "y ≠ 0",
        f"y ≠ ({ns}S1 : ℝ)",
        f"y ≠ ({ns}S2 : ℝ)",
        f"y ≠ ({ns}S3 : ℝ)",
        f"y ≠ ({ns}S4 : ℝ)",
    ]


def exclusion_args() -> str:
    return "hy0ne hy1ne hy2ne hy3ne hy4ne"


def chunk_v_theorem(ns: str, chunk_idx: int) -> list[str]:
    cname = f"{ns}RightChunk{chunk_idx:03d}"
    cert = f"{cname}Certificate"
    params = f"{cname}ParamsCertificate"
    thm = theorem_name(ns, f"right_chunk{chunk_idx:03d}_V_pos")
    return [
        f"def {params} : Bool :=",
        f"  allBoxesSameParams {cname} {ns}W1 {ns}W2 {ns}W3 {ns}W4 {ns}S1 {ns}S2 {ns}S3 {ns}S4",
        "",
        f"theorem {params}_eq_true :",
        f"    {params} = true := by",
        "  native_decide",
        "",
        f"theorem {thm}",
        "    {y : ℝ}",
        f"    (hy : y ∈ Icc ({cname}L : ℝ) ({cname}R : ℝ))",
        "    (hy0ne : y ≠ 0)",
        f"    (hy1ne : y ≠ ({ns}S1 : ℝ))",
        f"    (hy2ne : y ≠ ({ns}S2 : ℝ))",
        f"    (hy3ne : y ≠ ({ns}S3 : ℝ))",
        f"    (hy4ne : y ≠ ({ns}S4 : ℝ)) :",
        f"    0 < {ns}V y := by",
        f"  have hcert := {cert}_eq_true",
        f"  unfold {cert} at hcert",
        "  have hboxes := bool_left_of_and_eq_true hcert",
        "  have hcover := bool_right_of_and_eq_true hcert",
        f"  exact ratPotential_pos_of_allBoxesValid_covers_sameParams",
        f"    (boxes := {cname}) (lo := {cname}L) (hi := {cname}R)",
        f"    (w1 := {ns}W1) (w2 := {ns}W2) (w3 := {ns}W3) (w4 := {ns}W4)",
        f"    (s1 := {ns}S1) (s2 := {ns}S2) (s3 := {ns}S3) (s4 := {ns}S4)",
        f"    hboxes hcover {params}_eq_true hy {exclusion_args()}",
        "",
    ]


def right_cases(ns: str, chunk_count: int, indent: str = "  ") -> list[str]:
    lines: list[str] = []
    if chunk_count == 1:
        lines += [
            f"{indent}have hL : ({ns}RightChunk000L : ℝ) = ({ns}RightL : ℝ) := by",
            f"{indent}  norm_num [{ns}RightChunk000L, {ns}RightL]",
            f"{indent}have hR : ({ns}RightChunk000R : ℝ) = ({ns}RightR : ℝ) := by",
            f"{indent}  norm_num [{ns}RightChunk000R, {ns}RightR]",
            f"{indent}have hyc : y ∈ Icc ({ns}RightChunk000L : ℝ) ({ns}RightChunk000R : ℝ) := by",
            f"{indent}  constructor <;> linarith [hy.1, hy.2, hL, hR]",
            f"{indent}exact {theorem_name(ns, 'right_chunk000_V_pos')} hyc {exclusion_args()}",
        ]
        return lines

    for idx in range(chunk_count - 1):
        cname = f"{ns}RightChunk{idx:03d}"
        next_name = f"{ns}RightChunk{idx + 1:03d}"
        hname = f"h{idx}"
        lines += [
            f"{indent}by_cases {hname} : y ≤ ({cname}R : ℝ)",
            f"{indent}· have hyc : y ∈ Icc ({cname}L : ℝ) ({cname}R : ℝ) := by",
        ]
        if idx == 0:
            lines += [
                f"{indent}    have hL : ({cname}L : ℝ) = ({ns}RightL : ℝ) := by",
                f"{indent}      norm_num [{cname}L, {ns}RightL]",
                f"{indent}    constructor",
                f"{indent}    · linarith [hy.1, hL]",
                f"{indent}    · exact {hname}",
            ]
        else:
            prev = f"{ns}RightChunk{idx - 1:03d}"
            prev_h = f"h{idx - 1}"
            lines += [
                f"{indent}    have hprev : ({prev}R : ℝ) < y := lt_of_not_ge {prev_h}",
                f"{indent}    have hL : ({cname}L : ℝ) = ({prev}R : ℝ) := by",
                f"{indent}      norm_num [{cname}L, {prev}R]",
                f"{indent}    constructor",
                f"{indent}    · linarith [hprev, hL]",
                f"{indent}    · exact {hname}",
            ]
        lines += [
            f"{indent}  exact {theorem_name(ns, f'right_chunk{idx:03d}_V_pos')} hyc {exclusion_args()}",
            f"{indent}·",
        ]
        indent += "  "

    last = chunk_count - 1
    last_name = f"{ns}RightChunk{last:03d}"
    prev = f"{ns}RightChunk{last - 1:03d}"
    prev_h = f"h{last - 1}"
    lines += [
        f"{indent}have hprev : ({prev}R : ℝ) < y := lt_of_not_ge {prev_h}",
        f"{indent}have hL : ({last_name}L : ℝ) = ({prev}R : ℝ) := by",
        f"{indent}  norm_num [{last_name}L, {prev}R]",
        f"{indent}have hR : ({last_name}R : ℝ) = ({ns}RightR : ℝ) := by",
        f"{indent}  norm_num [{last_name}R, {ns}RightR]",
        f"{indent}have hyc : y ∈ Icc ({last_name}L : ℝ) ({last_name}R : ℝ) := by",
        f"{indent}  constructor",
        f"{indent}  · linarith [hprev, hL]",
        f"{indent}  · linarith [hy.2, hR]",
        f"{indent}exact {theorem_name(ns, f'right_chunk{last:03d}_V_pos')} hyc {exclusion_args()}",
    ]
    return lines


def generate_block(meta: dict) -> str:
    i = int(meta["block"])
    mod = module_name(i)
    ns = ns_name(i)
    weights = [rat_from_string(x) for x in meta["weights"]]
    shifts = [rat_from_string(x) for x in meta["shifts"]]
    chunk_count = math.ceil(int(meta["right_boxes"]) / 100)

    lines: list[str] = [
        "import Erdos1038Lean.LogBridge",
        f"import Erdos1038Lean.M1817475.{mod}",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 100000",
        "",
        "namespace Erdos1038Lean",
        "namespace M1817475",
        f"namespace {mod}",
        "",
        "open Set",
        "",
        f"def {ns}W1 : Rat := {rat(weights[0])}",
        f"def {ns}W2 : Rat := {rat(weights[1])}",
        f"def {ns}W3 : Rat := {rat(weights[2])}",
        f"def {ns}W4 : Rat := {rat(weights[3])}",
        f"def {ns}S1 : Rat := {rat(shifts[0])}",
        f"def {ns}S2 : Rat := {rat(shifts[1])}",
        f"def {ns}S3 : Rat := {rat(shifts[2])}",
        f"def {ns}S4 : Rat := {rat(shifts[3])}",
        "",
        f"noncomputable def {ns}V (y : ℝ) : ℝ :=",
        f"  ratPotential {ns}W1 {ns}W2 {ns}W3 {ns}W4 {ns}S1 {ns}S2 {ns}S3 {ns}S4 y",
        "",
        f"def {ns}LeftParamsCertificate : Bool :=",
        f"  allBoxesSameParams {ns}LeftBoxes {ns}W1 {ns}W2 {ns}W3 {ns}W4 {ns}S1 {ns}S2 {ns}S3 {ns}S4",
        "",
        f"theorem {ns}LeftParamsCertificate_eq_true :",
        f"    {ns}LeftParamsCertificate = true := by",
        "  native_decide",
        "",
        f"theorem {theorem_name(ns, 'left_V_pos')}",
        "    {y : ℝ}",
        f"    (hy : y ∈ Icc ({ns}LeftL : ℝ) ({ns}LeftR : ℝ))",
        "    (hy0ne : y ≠ 0)",
        f"    (hy1ne : y ≠ ({ns}S1 : ℝ))",
        f"    (hy2ne : y ≠ ({ns}S2 : ℝ))",
        f"    (hy3ne : y ≠ ({ns}S3 : ℝ))",
        f"    (hy4ne : y ≠ ({ns}S4 : ℝ)) :",
        f"    0 < {ns}V y := by",
        f"  have hcert := {ns}LeftCertificate_eq_true",
        f"  unfold {ns}LeftCertificate at hcert",
        "  have hboxes := bool_left_of_and_eq_true hcert",
        "  have hcover := bool_right_of_and_eq_true hcert",
        f"  exact ratPotential_pos_of_allBoxesValid_covers_sameParams",
        f"    (boxes := {ns}LeftBoxes) (lo := {ns}LeftL) (hi := {ns}LeftR)",
        f"    (w1 := {ns}W1) (w2 := {ns}W2) (w3 := {ns}W3) (w4 := {ns}W4)",
        f"    (s1 := {ns}S1) (s2 := {ns}S2) (s3 := {ns}S3) (s4 := {ns}S4)",
        f"    hboxes hcover {ns}LeftParamsCertificate_eq_true hy {exclusion_args()}",
        "",
    ]

    for idx in range(chunk_count):
        lines.extend(chunk_v_theorem(ns, idx))

    lines += [
        f"theorem {theorem_name(ns, 'right_V_pos')}",
        "    {y : ℝ}",
        f"    (hy : y ∈ Icc ({ns}RightL : ℝ) ({ns}RightR : ℝ))",
        "    (hy0ne : y ≠ 0)",
        f"    (hy1ne : y ≠ ({ns}S1 : ℝ))",
        f"    (hy2ne : y ≠ ({ns}S2 : ℝ))",
        f"    (hy3ne : y ≠ ({ns}S3 : ℝ))",
        f"    (hy4ne : y ≠ ({ns}S4 : ℝ)) :",
        f"    0 < {ns}V y := by",
    ]
    lines.extend(right_cases(ns, chunk_count))
    lines += [
        "",
        f"def {ns}_reallog_certificate : Prop :=",
        f"  (∀ {{y : ℝ}}, y ∈ Icc ({ns}LeftL : ℝ) ({ns}LeftR : ℝ) →",
        f"    y ≠ 0 → y ≠ ({ns}S1 : ℝ) → y ≠ ({ns}S2 : ℝ) →",
        f"    y ≠ ({ns}S3 : ℝ) → y ≠ ({ns}S4 : ℝ) → 0 < {ns}V y) /\\",
        f"  (∀ {{y : ℝ}}, y ∈ Icc ({ns}RightL : ℝ) ({ns}RightR : ℝ) →",
        f"    y ≠ 0 → y ≠ ({ns}S1 : ℝ) → y ≠ ({ns}S2 : ℝ) →",
        f"    y ≠ ({ns}S3 : ℝ) → y ≠ ({ns}S4 : ℝ) → 0 < {ns}V y)",
        "",
        f"theorem {ns}_reallog_certificate_proof :",
        f"    {ns}_reallog_certificate := by",
        f"  exact ⟨{theorem_name(ns, 'left_V_pos')}, {theorem_name(ns, 'right_V_pos')}⟩",
        "",
        f"end {mod}",
        "end M1817475",
        "end Erdos1038Lean",
        "",
    ]
    return "\n".join(lines)


def meta_from_certificate(cert: dict, out_dir: Path, i: int) -> dict:
    mod = module_name(i)
    ns = ns_name(i)
    m_value = Fraction(Decimal(str(cert["M"])))
    base = Fraction(Decimal(str(cert["base"])))
    k_blocks = int(cert["K"])
    h = Fraction(Decimal(str(cert.get("h", str(m_value - base))))) if "h" in cert else (m_value - base) / k_blocks
    starts = [Fraction(Decimal(str(x))) for x in cert["lane_starts_s"]]
    permutations = [[int(x) for x in lane] for lane in cert["permutations"]]
    a = m_value - i * h
    shifts = [a + starts[j] + permutations[j][i] * h for j in range(4)]
    weights = [Fraction(Decimal(str(x))) for x in cert["weights"][i]]
    text = (out_dir / f"{mod}.lean").read_text()
    chunk_count = len(re.findall(rf"def {ns}RightChunk\d{{3}} : List RatBox", text))
    if chunk_count == 0:
        raise RuntimeError(f"no right chunks found in {mod}.lean")
    return {
        "block": i,
        "weights": [str(x) for x in weights],
        "shifts": [str(x) for x in shifts],
        "right_boxes": chunk_count * 100,
    }


def nested_pair(terms: list[str]) -> str:
    if not terms:
        return "trivial"
    if len(terms) == 1:
        return terms[0]
    return f"⟨{terms[0]}, {nested_pair(terms[1:])}⟩"


def generate_aggregate(out_dir: Path, count: int) -> None:
    imports = [f"import Erdos1038Lean.M1817475.{module_name(i)}LogBridge" for i in range(count)]
    props = [
        f"{module_name(i)}.{ns_name(i)}_reallog_certificate"
        for i in range(count)
    ]
    proofs = [
        f"{module_name(i)}.{ns_name(i)}_reallog_certificate_proof"
        for i in range(count)
    ]
    text = "\n".join(
        imports
        + [
            "",
            "set_option maxHeartbeats 0",
            "set_option maxRecDepth 100000",
            "",
            "namespace Erdos1038Lean",
            "namespace M1817475",
            "",
            "/-- Aggregate real-log positivity certificate for the 560 generated blocks.",
            "",
            "This proves the block-level logarithmic-potential positivity statements",
            "for the generated finite-atom certificate, away from singular atom",
            "locations.  It is still downstream of the normalized-support reduction.",
            "-/",
            "def all560_reallog_certificate : Prop :=",
            "    " + " /\\\n    ".join(props),
            "",
            "theorem all560_reallog_certificate_proof :",
            "    all560_reallog_certificate := by",
            f"  exact {nested_pair(proofs)}",
            "",
            "end M1817475",
            "end Erdos1038Lean",
            "",
        ]
    )
    (out_dir / "AllBlocksLogBridge.lean").write_text(text)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_DIR)
    parser.add_argument("--input", type=Path, default=DEFAULT_CERT)
    parser.add_argument("--block", type=int)
    parser.add_argument("--count", type=int, default=560)
    parser.add_argument("--aggregate", action="store_true")
    args = parser.parse_args()

    if args.block is None:
        block_indices = list(range(args.count))
    else:
        block_indices = [args.block]

    cert = json.loads(args.input.read_text(), parse_float=Decimal)

    for i in block_indices:
        mod = module_name(i)
        meta_path = args.out_dir / f"{mod}.json"
        if meta_path.exists():
            meta = json.loads(meta_path.read_text())
        else:
            meta = meta_from_certificate(cert, args.out_dir, i)
        (args.out_dir / f"{mod}LogBridge.lean").write_text(generate_block(meta))

    if args.aggregate:
        generate_aggregate(args.out_dir, args.count)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
