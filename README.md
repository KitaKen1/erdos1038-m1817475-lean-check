# Attempted computational check for a reduced finite-atom certificate for #1038 at M = 1.817475

This is an attempt repository for a Lean-based computational check of the
all-560-block rational manifest for a proposed reduced finite-atom certificate
for Erdos Problems #1038 [Reference 1], at `M = 1.817475`.

The certificate follows the finite-atom / piecewise-certificate route developed
in the #1038 discussion, including Hua Xu's `M = 1.814600` certificate work
[Reference 2], and tests an assignment/permutation-style variant suggested in
the subsequent discussion [Reference 3].

It does **not** claim a full Lean proof of the original #1038 problem, and it
should be read as an experimental verification attempt.  The outer standard
reduction and the full `Real.log` lower-bound bridge are still outside the
current package.

For additional mathematical and computational background, see Appendix A and
Appendix B below.

## Computational check architecture in this repository

The code in this repository has two parts.

1. Python generates the proposed finite-certificate data for `M = 1.817475`.
2. Lean then checks the generated rational manifest corresponding to the
   required `V_i(y) > 0` block conditions.

### 1. Python generation part

Python is used to generate the proposed `M = 1.817475` certificate data.  This
includes the atom positions, atom weights, block assignments, permutation
lanes, rational boxes, and submitted lower-bound values.

Mathematically, the candidate data are obtained by the following steps.

1. Fix a target lower bound `M` and the split value `B = 1.708`.
2. Divide the tail interval `[B, M]` into `K = 560` small blocks
   `[C_i, A_i]`.
3. On each block, define a five-atom test potential: one atom at `0` and four
   shifted atoms.
4. Implement the assignment/permutation idea by choosing shifted-atom positions
   through four permutation lanes.
5. For each block, choose nonnegative weights so that the resulting potential
   `V_i(y)` is positive on the two required domains.
6. The resulting block data are the endpoints, shifted atom positions, weights,
   margins, and minimizing points for all `560` blocks.

This generation step is not formally verified in Lean.

### 2. Lean verification part

Lean is used after the candidate data have been turned into generated Lean
source files.  It does not search for atoms or weights.  It checks the
published rational manifest for the proposed `M = 1.817475` certificate.

Mathematically, the Lean check has the following shape.

1. For each block `i`, take the generated rational endpoints, shifted atom
   positions, weights, and box lists as exact rational data.
2. Replace each required domain `[C_i - 1, A_i - 1]` and `[C_i, A_i + 1]` by a
   finite list of rational boxes.
3. For each box `[L,R]`, use stored rational distance bounds `D0,...,D4` and a
   submitted rational lower bound `LB`.
4. Check, using exact rational arithmetic, that the boxes cover the required
   domains, the endpoint-distance bounds are valid, and every submitted `LB` is
   positive.
5. Prove one block certificate proposition for each of the `560` blocks.
6. Aggregate the `560` block certificates into one Lean theorem.

The current generated files use `float` lower-bound mode.  In this mode, Python
is still part of the trust boundary for the submitted lower-bound values
themselves.

## How to check the code

There are three practical checks.

First, run the independent numerical audits of the JSON certificate:

```bash
scripts/run_basic_checks.sh
```

This runs both the standard-library checker and the higher-precision Decimal
checker against:

```text
certificates/ehp1038_M1817475_v2_experimental_certificate.json
```

The expected result is that both summaries report:

```text
bad_required_blocks: 0
all_required_blocks_ok: true
```

Second, run the Lean package check:

```bash
scripts/check_pure_lean.sh
```

This builds the generated Lean files and checks the aggregate theorem in:

```text
Erdos1038Lean/M1817475/AllBlocks.lean
```

Third, if the generated Lean files need to be recreated from the JSON
certificate, run:

```bash
python3 scripts/generate_all_blocks.py
python3 scripts/make_all560_lean4web_exports.py
```

Regenerating the floating-point candidate certificate itself is a separate
experimental/search step and requires NumPy/SciPy.  The Lean check does not
trust that search script directly; it checks the generated rational manifest
currently present in the repository.

## Check by Lean4Web

For checking, self-contained Lean4Web files are provided for all `560`
individual blocks:

```text
lean4web/all560_blocks/Block000_lean4web.lean
...
lean4web/all560_blocks/Block559_lean4web.lean
```

Each file can be pasted into Lean4Web and checked independently.  Passing one
of these files means that Lean accepted the generated rational data for that
block.  In the intended interpretation, this is the blockwise rational-manifest
check corresponding to the required condition `V_i(y) > 0` on that block's
required domains.

If all `560` block files pass, then the blockwise content of the proposed
all-560-block rational-manifest certificate at `M = 1.817475` has been checked.
The Lake theorem in this repository then aggregates those `560` block
certificates into the single all-block certificate theorem.

These are checks of generated rational data.  They are not, by themselves, a
full Lean proof of the original #1038 problem, nor do they remove the current
trust boundary for the submitted `Real.log` lower-bound values.

## File layout

The repository is organized as follows.

```text
README.md                         main description and reproduction guide
.gitignore                        local build/cache ignore rules
LICENSE                           repository license
lakefile.toml                     Lean/Lake package definition
lean-toolchain                    Lean version pin
requirements.txt                  optional Python deps for certificate search

Erdos1038Lean.lean                Lean library entry point
Erdos1038Lean/
  RationalKernel.lean             exact rational box-checking kernel
  ReducedStatement.lean           informal/reduced statement wrappers
  M1817475/
    Block000.lean ... Block559.lean   generated per-block Lean checks
    AllBlocks.lean                    aggregate theorem over all 560 blocks
    all560_manifest.json              summary of generated block files

certificates/
  ehp1038_M1817475_v2_experimental_certificate.json
                                  floating-point candidate certificate data

scripts/
  gen_fast_custom.py              floating-point candidate generator/search
  ehp1038_research.py             numerical helper routines for the generator
  verify_permutation_certificate_stdlib.py
                                  independent stdlib numerical checker
  verify_permutation_certificate_decimal.py
                                  higher-precision Decimal numerical checker
  generate_all_blocks.py          JSON certificate to all Lean block files
  generate_rational_box_chunk.py  rational-box Lean code generator
  make_all560_lean4web_exports.py self-contained Lean4Web exporter
  run_basic_checks.sh             runs the numerical audits
  check_pure_lean.sh              runs the Lean/Lake verification

audits/reproduced/
  M1817475_stdlib_summary.json    reproduced stdlib audit summary
  M1817475_stdlib_margins.csv     reproduced stdlib per-block margins
  M1817475_decimal90_summary.json reproduced Decimal90 audit summary
  M1817475_decimal90_margins.csv  reproduced Decimal90 per-block margins

lean4web/
  all560_blocks/
    Block000_lean4web.lean ... Block559_lean4web.lean
                                  self-contained per-block Lean4Web files
```

The generated Lean block files are intentionally committed as source files, so
that the rational data can be inspected directly and checked without rerunning
the Python search.

## Appendix A: Mathematical background

This appendix is AI-assisted explanatory background and has not yet been
carefully audited.  It should not be treated as part of the formal claim of
this repository.

To obtain a lower bound for the original problem, the following reduction is
used in the #1038 discussion.

> **Reduced logarithmic-potential statement.** For the lower bound, it is
> enough to prove `length(E_mu) >= M` for every admissible normalized root
> distribution `mu`, after the standard logarithmic-potential reduction.

To make this reduced statement computer-checkable, the following finite
certificate route is used.

> **Finite-certificate sufficient condition.** For the lower bound, it is
> enough to produce certificate data for `M` such that all required block
> inequalities `V_i(y) > 0` hold on their required domains, together with the
> required sweep/counting bookkeeping.

Hua Xu developed this route using a finite-atom dual-forcing method: in each
piece, finitely many test atoms with nonnegative weights are chosen so that the
positivity of their weighted logarithmic potential forces a hit in `E_mu`.  In
the #1038 discussion, this piecewise five-atom certificate pushed the reported
certificate value to `M = 1.814600` [Reference 2].

In response to this direction, catsflowers5544 suggested that the next search
should add assignment/permutation constraints to the piecewise-shift search
[Reference 3].  The four-lane construction used here is an implementation of
that suggestion, not a claim that Reference 3 specified these exact lanes.

Following that discussion, this repository checks a proposed certificate at
`M = 1.817475`.  This is a verification of the generated finite-certificate
data, not a full Lean proof of the original #1038 problem or of the analytic
reduction leading to the reduced statement.

## Appendix B: Computational check background

This appendix is AI-assisted explanatory background and has not yet been
carefully audited.  It should not be treated as part of the formal claim of
this repository.

Hua Xu's piecewise five-atom method turns the reduced statement into many
one-variable positivity checks.  For each block, the certificate uses one
implicit atom at `0` and four shifted atoms.  In schematic form, the block
potential is

```text
V_i(y) = log(1 / |y|)
       + w1 log(1 / |y - s1|)
       + w2 log(1 / |y - s2|)
       + w3 log(1 / |y - s3|)
       + w4 log(1 / |y - s4|).
```

The task for block `i` is to certify that `V_i(y) > 0` on the two required
domains for that block:

```text
[C_i - 1, A_i - 1]  and  [C_i, A_i + 1].
```

In this candidate, the tail interval from the base value `B = 1.708` to
`M = 1.817475` is split into `K = 560` blocks.  Each generated block file
therefore contains the rational endpoints `A_i, C_i`, the four shifted atom
locations `s1,...,s4`, the nonnegative weights `w1,...,w4`, and rational boxes
covering the two required domains.

The suggestion attributed to catsflowers5544 is not merely to increase the
number of blocks.  It is to add assignment/permutation constraints to the
piecewise-shift search.  In this implementation, that suggestion is represented
by four permutation lanes: each shifted-atom lane assigns the `560` block
indices by a permutation of `0,...,559`.  This lets the search reassign shifted
atoms across blocks while keeping the sweep/counting bookkeeping structured.

## AI usage disclosure
The code and documentation were prepared with assistance from Codex 5.5
using xhigh reasoning, and ChatGPT 5.5 Pro.

## References
[Reference 1] Erdos Problems, "#1038" forum thread.
https://www.erdosproblems.com/forum/thread/1038

[Reference 2] Hua Xu, comment on the Erdos Problems #1038 forum thread,
09:49 on 02 May 2026, describing the finite-atom / piecewise five-atom
certificate route and the `M = 1.814600` certificate.
https://www.erdosproblems.com/forum/thread/1038

[Reference 3] catsflowers5544, comment on the Erdos Problems #1038 forum
thread, 12:53 on 27 May 2026, suggesting assignment/permutation constraints
for the next search direction.
https://www.erdosproblems.com/forum/thread/1038
