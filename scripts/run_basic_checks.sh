#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

python3 scripts/verify_permutation_certificate_stdlib.py \
  --input certificates/ehp1038_M1817475_v2_experimental_certificate.json \
  --out-json audits/reproduced/M1817475_stdlib_summary.json \
  --out-csv audits/reproduced/M1817475_stdlib_margins.csv

python3 scripts/verify_permutation_certificate_decimal.py \
  --input certificates/ehp1038_M1817475_v2_experimental_certificate.json \
  --precision 90 \
  --iterations 180 \
  --out-json audits/reproduced/M1817475_decimal90_summary.json \
  --out-csv audits/reproduced/M1817475_decimal90_margins.csv
