#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scanner="$repo_root/scripts/check-lean-proof-policy.py"
fixture_dir="$(mktemp -d)"
trap 'rm -rf "$fixture_dir"' EXIT

old_pattern='(^|[^[:alnum:]_])(sorry|admit|native_decide|CertifiedArtifact)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]|set_option[[:space:]]+maxHeartbeats[[:space:]]+0'

cat > "$fixture_dir/private-axiom.lean" <<'EOF'
private axiom hiddenEscape : True
EOF

cat > "$fixture_dir/split-heartbeats.lean" <<'EOF'
set_option
  maxHeartbeats 0
EOF

# Regression controls: both constructs escaped the previous line-oriented grep.
! grep -nE "$old_pattern" "$fixture_dir/private-axiom.lean"
! grep -nE "$old_pattern" "$fixture_dir/split-heartbeats.lean"

expect_rejected() {
  local fixture="$1"
  local expected="$2"
  local stderr_file="$fixture_dir/stderr"
  if python3 "$scanner" "$fixture" 2> "$stderr_file"; then
    printf 'expected scanner to reject %s\n' "$fixture" >&2
    exit 1
  fi
  grep -Fq "$expected" "$stderr_file"
}

expect_rejected "$fixture_dir/private-axiom.lean" 'forbidden axiom declaration'
expect_rejected "$fixture_dir/split-heartbeats.lean" 'unlimited maxHeartbeats'

cat > "$fixture_dir/comments-and-strings.lean" <<'EOF'
-- private axiom mentionedInComment : True
/- Nested comments may mention set_option
   maxHeartbeats 0 and /- sorry -/ safely. -/
def policyWords : String := "admit native_decide CertifiedArtifact"
set_option maxHeartbeats 1000 in
example : True := by trivial
EOF

python3 "$scanner" "$fixture_dir/comments-and-strings.lean"
printf 'Lean proof-policy scanner self-test: PASS\n'
