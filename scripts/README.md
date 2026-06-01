# Python scripts

This directory contains the non-Lean side of the attempted certificate.

The Python code has two different roles.

1. `gen_fast_custom.py` and `ehp1038_research.py` generate the floating-point
   candidate certificate data.  This is the experimental/search part.
2. `verify_permutation_certificate_stdlib.py` and
   `verify_permutation_certificate_decimal.py` independently recompute the
   blockwise margins from a certificate JSON file.  These are numerical
   checkers, not formal proofs.
3. `generate_all_blocks.py` and `generate_rational_box_chunk.py` convert the
   JSON certificate into generated Lean files containing rational boxes and
   rational lower-bound values.
4. `make_all560_lean4web_exports.py` builds the self-contained Lean4Web files
   under `lean4web/all560_blocks/`.
5. `check_pure_lean.sh` runs the Lean/Lake check of the generated files.

The main certificate used by this repository is:

```text
certificates/ehp1038_M1817475_v2_experimental_certificate.json
```

Quick numerical audit:

```bash
python3 scripts/verify_permutation_certificate_stdlib.py \
  --input certificates/ehp1038_M1817475_v2_experimental_certificate.json
```

Regenerating the candidate certificate requires NumPy/SciPy.  The Lean check
itself does not trust the Python generator; it checks the generated rational
manifest files that are already present in `Erdos1038Lean/M1817475/`.
