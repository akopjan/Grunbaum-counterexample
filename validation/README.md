# Validation status

- `source_audit.json` / `source_audit.log`: static scan of proof-development
  Lean sources, including `Solution.lean` and excluding the deliberate
  `Challenge.lean` hole.
- `preparation_status.json`: machine-readable statement of checks.

To verify, run `lake build` and `./scripts/verify.sh` from a clean checkout.
