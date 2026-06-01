#!/usr/bin/env python3
"""Create self-contained Lean4Web exports for the generated 560 block files."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
KERNEL = ROOT / "Erdos1038Lean" / "RationalKernel.lean"
BLOCK_DIR = ROOT / "Erdos1038Lean" / "M1817475"
OUT = ROOT / "lean4web" / "all560_blocks"


def strip_imports(text: str) -> str:
    return "\n".join(line for line in text.splitlines() if not line.startswith("import "))


def module_name(i: int) -> str:
    return "Block196" if i == 196 else f"Block{i:03d}"


def ns_name(i: int) -> str:
    return "block196" if i == 196 else f"block{i:03d}"


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    kernel = strip_imports(KERNEL.read_text())

    for i in range(560):
        mod = module_name(i)
        ns = ns_name(i)
        block = strip_imports((BLOCK_DIR / f"{mod}.lean").read_text())
        text = "\n".join(
            [
                "/-",
                "Self-contained Lean4Web paste file.",
                f"Block {i} rational-manifest check for the M=1.817475 candidate.",
                "",
                "This checks the rational manifest layer for this block:",
                "box coverage, rational endpoint-distance bounds, and positivity",
                "of submitted lower-bound rationals.  It does not include the",
                "Mathlib Real.log bridge.",
                "-/",
                "",
                kernel,
                "",
                block,
                "",
                f"#check Erdos1038Lean.M1817475.{mod}.{ns}_rational_certificate_proof",
                "",
            ]
        )
        (OUT / f"{mod}_lean4web.lean").write_text(text)

    index = """# All-560 Lean4Web block exports

This directory contains self-contained Lean files:

```text
Block000_lean4web.lean
...
Block559_lean4web.lean
```

Each file can be pasted into Lean4Web independently.  Each file checks one
generated block of the `M = 1.817475` rational manifest.

The true all-block aggregate theorem is the Lake/import-based file:

```text
Erdos1038Lean/M1817475/AllBlocks.lean
```

That aggregate was checked locally by:

```bash
cd Forgithubpublication
scripts/check_pure_lean.sh
```

Lean4Web is useful for manually inspecting and checking individual block files.
It is not a good substitute for the Lake package when checking all 560 imports
in one session.

Current caveat: these files check the rational-manifest layer, not the Mathlib
`Real.log` bridge.
"""
    (OUT / "README.md").write_text(index)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
