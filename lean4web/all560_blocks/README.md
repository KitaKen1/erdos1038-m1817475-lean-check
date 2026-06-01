# All-560 Lean4Web block exports

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
