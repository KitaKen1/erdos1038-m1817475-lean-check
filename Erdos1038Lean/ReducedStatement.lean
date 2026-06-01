import Erdos1038Lean.M1817475.AllBlocks

/-!
# Reduced statement entry points

This file records the intended theorem names for the Lean certificate package.
The current package contains all generated `Block000` through `Block559`
rational-manifest checks and an aggregate theorem for all blocks.

This is still the reduced finite rational-manifest layer.  It does not prove
the analytic `Real.log` bridge to the original problem.
-/

namespace Erdos1038Lean

namespace M1817475

/-- First Lean-checked bottleneck block for the reduced finite-atom certificate. -/
theorem reduced_statement_block196_smoke :
    Block196.block196_rational_certificate :=
  Block196.block196_rational_certificate_proof

/--
All 560 generated block certificates for the M = 1.817475 rational manifest.

This theorem aggregates the block-level checks.  It is deliberately named
`rational_manifest`, not `proof_of_original_problem`, because the analytic
`Real.log` bridge is not yet included.
-/
theorem reduced_statement_all560_rational_manifest :
    all560_rational_certificate :=
  all560_rational_certificate_proof

end M1817475

end Erdos1038Lean
