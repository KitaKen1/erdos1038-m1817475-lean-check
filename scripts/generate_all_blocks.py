#!/usr/bin/env python3
"""Generate all 560 Lean block files and the aggregate manifest theorem.

This script deliberately generates source files, not opaque build artifacts.
The generated Lean files expose the rational certificate data so that a reader
can inspect the numbers and ask Lean to check the finite rational conditions.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal
from pathlib import Path

from generate_rational_box_chunk import DEFAULT_CERT, DEFAULT_OUT, generate_block


ROOT = Path(__file__).resolve().parents[1]


def module_name(i: int) -> str:
    return "Block196" if i == 196 else f"Block{i:03d}"


def ns_name(i: int) -> str:
    return "block196" if i == 196 else f"block{i:03d}"


def nested_pair(terms: list[str]) -> str:
    if not terms:
        return "trivial"
    if len(terms) == 1:
        return terms[0]
    return f"⟨{terms[0]}, {nested_pair(terms[1:])}⟩"


def generate_aggregate(out_dir: Path, count: int) -> None:
    imports = [f"import Erdos1038Lean.M1817475.{module_name(i)}" for i in range(count)]
    prop_terms = [
        f"{module_name(i)}.{ns_name(i)}_rational_certificate"
        for i in range(count)
    ]
    proof_terms = [
        f"{module_name(i)}.{ns_name(i)}_rational_certificate_proof"
        for i in range(count)
    ]
    prop_body = " /\\\n    ".join(prop_terms)
    proof_body = nested_pair(proof_terms)
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
            "/--",
            "Aggregate proposition for the generated 560-block rational manifest.",
            "",
            "This is still the reduced finite rational-certificate layer.  It does",
            "not include the analytic `Real.log` bridge to the original problem.",
            "-/",
            "def all560_rational_certificate : Prop :=",
            f"    {prop_body}",
            "",
            "theorem all560_rational_certificate_proof :",
            "    all560_rational_certificate := by",
            f"  exact {proof_body}",
            "",
            "end M1817475",
            "end Erdos1038Lean",
            "",
        ]
    )
    (out_dir / "AllBlocks.lean").write_text(text)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_CERT)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--count", type=int, default=560)
    parser.add_argument("--threshold", type=float, default=1e-7)
    parser.add_argument("--max-depth", type=int, default=32)
    parser.add_argument("--npos", type=int, default=150)
    parser.add_argument("--nneg", type=int, default=150)
    parser.add_argument("--lb-mode", choices=["float", "exact"], default="float")
    args = parser.parse_args()

    cert = json.loads(args.input.read_text(), parse_float=Decimal)
    args.out_dir.mkdir(parents=True, exist_ok=True)

    summaries = []
    for i in range(args.count):
        text, meta = generate_block(
            cert,
            i,
            threshold=args.threshold,
            max_depth=args.max_depth,
            npos=args.npos,
            nneg=args.nneg,
            lb_mode=args.lb_mode,
        )
        name = module_name(i)
        (args.out_dir / f"{name}.lean").write_text(text)
        (args.out_dir / f"{name}.json").write_text(json.dumps(meta, indent=2))
        summaries.append(meta)

    generate_aggregate(args.out_dir, args.count)
    manifest = {
        "count": args.count,
        "lower_bound_mode": args.lb_mode,
        "total_left_boxes": sum(int(x["left_boxes"]) for x in summaries),
        "total_right_boxes": sum(int(x["right_boxes"]) for x in summaries),
        "max_left_boxes": max(int(x["left_boxes"]) for x in summaries),
        "max_right_boxes": max(int(x["right_boxes"]) for x in summaries),
        "max_right_block": max(summaries, key=lambda x: int(x["right_boxes"]))["block"],
        "note": (
            "This manifest describes generated Lean source files for the reduced "
            "finite rational-certificate layer, not a full formalization of the "
            "analytic reduction."
        ),
    }
    (args.out_dir / "all560_manifest.json").write_text(json.dumps(manifest, indent=2))
    print(json.dumps(manifest, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
