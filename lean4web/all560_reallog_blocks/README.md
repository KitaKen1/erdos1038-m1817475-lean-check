# All-560 Lean4Web real-log block exports

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
