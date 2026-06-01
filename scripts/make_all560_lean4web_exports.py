#!/usr/bin/env python3
"""Create self-contained Lean4Web exports for the generated 560 block files.

Two export families are produced:

* ``lean4web/all560_blocks`` contains compact rational-manifest checks.
* ``lean4web/all560_reallog_blocks`` contains larger Mathlib files that also
  include the ``Real.log`` bridge and expose block-level ``V_i(y) > 0``
  theorems.
"""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
KERNEL = ROOT / "Erdos1038Lean" / "RationalKernel.lean"
LOG_BRIDGE = ROOT / "Erdos1038Lean" / "LogBridge.lean"
BLOCK_DIR = ROOT / "Erdos1038Lean" / "M1817475"
RATIONAL_OUT = ROOT / "lean4web" / "all560_blocks"
REALLOG_OUT = ROOT / "lean4web" / "all560_reallog_blocks"


def strip_imports(text: str) -> str:
    return "\n".join(line for line in text.splitlines() if not line.startswith("import "))


def module_name(i: int) -> str:
    return "Block196" if i == 196 else f"Block{i:03d}"


def ns_name(i: int) -> str:
    return "block196" if i == 196 else f"block{i:03d}"


def write_rational_exports(kernel: str) -> None:
    RATIONAL_OUT.mkdir(parents=True, exist_ok=True)

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
                "of Lean-recomputed rational atanh/log lower-bound values.",
                "It does not include the Mathlib Real.log bridge.",
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
        (RATIONAL_OUT / f"{mod}_lean4web.lean").write_text(text)

    index = """# All-560 Lean4Web block exports

This directory contains self-contained Lean files:

```text
Block000_lean4web.lean
...
Block559_lean4web.lean
```

Each file can be pasted into Lean4Web independently.  Each file checks one
generated block of the `M = 1.817475` rational manifest.

The true all-block aggregate theorems are the Lake/import-based files:

```text
Erdos1038Lean/M1817475/AllBlocks.lean
Erdos1038Lean/M1817475/AllBlocksLogBridge.lean
```

That aggregate was checked locally by:

```bash
cd Forgithubpublication
scripts/check_pure_lean.sh
```

Lean4Web is useful for manually inspecting and checking individual block files.
It is not a good substitute for the Lake package when checking all 560 imports
in one session.

Current caveat: these Lean4Web files check the rational-manifest layer with
Lean-recomputed rational atanh/log lower-bound values.  They still do not
include the Mathlib `Real.log` bridge or the block-level `V_i(y) > 0`
theorems.  Those stronger real-log checks are in the sibling directory:

```text
lean4web/all560_reallog_blocks/
```
"""
    (RATIONAL_OUT / "README.md").write_text(index)


def write_reallog_exports(kernel: str, log_bridge: str) -> None:
    REALLOG_OUT.mkdir(parents=True, exist_ok=True)

    for i in range(560):
        mod = module_name(i)
        ns = ns_name(i)
        block = strip_imports((BLOCK_DIR / f"{mod}.lean").read_text())
        bridge = strip_imports((BLOCK_DIR / f"{mod}LogBridge.lean").read_text())
        text = "\n".join(
            [
                "/-",
                "Self-contained Lean4Web paste file.",
                f"Block {i} real-log V_i(y) > 0 check for the M=1.817475 candidate.",
                "",
                "This file includes the rational kernel, the generated block data,",
                "and the Mathlib Real.log bridge.  The final #check lines expose",
                "the block-level theorem whose type contains `0 < block...V y`.",
                "",
                "This is still only a block-level reduced-certificate check: it",
                "does not formalize the outer reduction from the original #1038",
                "problem, and the theorem excludes the singular atom locations.",
                "-/",
                "",
                "import Mathlib",
                "",
                kernel,
                "",
                log_bridge,
                "",
                block,
                "",
                bridge,
                "",
                f"#check Erdos1038Lean.M1817475.{mod}.{ns}V",
                f"#check Erdos1038Lean.M1817475.{mod}.{ns}_left_V_pos",
                f"#check Erdos1038Lean.M1817475.{mod}.{ns}_right_V_pos",
                f"#check Erdos1038Lean.M1817475.{mod}.{ns}_reallog_certificate_proof",
                "",
            ]
        )
        (REALLOG_OUT / f"{mod}_reallog_lean4web.lean").write_text(text)

    index = """# All-560 Lean4Web real-log block exports

This directory contains larger self-contained Lean4Web files:

```text
Block000_reallog_lean4web.lean
...
Block559_reallog_lean4web.lean
```

Each file can be pasted into Lean4Web independently.  Unlike the compact
files in `lean4web/all560_blocks`, these files import Mathlib and include the
`Real.log` bridge.  The final `#check` lines show the block-level theorem
types, including statements of the form:

```text
0 < blockNNNV y
```

The intended human check is:

1. paste one file into Lean4Web;
2. wait until Lean finishes;
3. confirm that `blockNNN_left_V_pos`, `blockNNN_right_V_pos`, and
   `blockNNN_reallog_certificate_proof` are accepted.

The all-560 aggregate theorem is still checked more practically by the local
Lake package:

```text
Erdos1038Lean/M1817475/AllBlocksLogBridge.lean
```

Caveat: these are block-level reduced-certificate checks.  They do not
formalize the outer reduction from the original #1038 problem, and the
real-log theorem excludes singular atom locations.
"""
    (REALLOG_OUT / "README.md").write_text(index)


def main() -> int:
    kernel = strip_imports(KERNEL.read_text())
    log_bridge = strip_imports(LOG_BRIDGE.read_text())
    write_rational_exports(kernel)
    write_reallog_exports(kernel, log_bridge)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
