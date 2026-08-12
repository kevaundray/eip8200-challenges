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

cat > "$fixture_dir/interpolated-sorry.lean" <<'EOF'
def escapedProof : String := s!"{(by sorry : Nat)}"
EOF
expect_rejected "$fixture_dir/interpolated-sorry.lean" 'forbidden proof mechanism: sorry'

cat > "$fixture_dir/message-interpolated-sorry.lean" <<'EOF'
#check m!"{(by sorry : Nat)}"
EOF
expect_rejected "$fixture_dir/message-interpolated-sorry.lean" 'forbidden proof mechanism: sorry'

cat > "$fixture_dir/format-interpolated-sorry.lean" <<'EOF'
#check f!"{(by sorry : Nat)}"
EOF
expect_rejected "$fixture_dir/format-interpolated-sorry.lean" 'forbidden proof mechanism: sorry'

cat > "$fixture_dir/parser-interpolated-sorry.lean" <<'EOF'
macro "policyProbe " message:interpolatedStr(term) : command =>
  `(command| #check $message)
policyProbe "{(by sorry : Nat)}"
EOF
expect_rejected "$fixture_dir/parser-interpolated-sorry.lean" 'forbidden proof mechanism: sorry'

for hashes in '#' '###' '######'; do
  fixture="$fixture_dir/raw-${#hashes}-then-sorry.lean"
  printf 'def raw : String := r%s"quotes " and policy words sorry axiom"%s\n' \
    "$hashes" "$hashes" > "$fixture"
  printf 'example : True := by sorry\n' >> "$fixture"
  expect_rejected "$fixture" 'forbidden proof mechanism: sorry'
done

cat > "$fixture_dir/sorry-ax.lean" <<'EOF'
example : True := by sorryAx (synthetic := true)
EOF
expect_rejected "$fixture_dir/sorry-ax.lean" 'forbidden proof mechanism: sorryAx'

cat > "$fixture_dir/operator-adjacent-sorry.lean" <<'EOF'
#check 1+sorry
EOF
expect_rejected "$fixture_dir/operator-adjacent-sorry.lean" 'forbidden proof mechanism: sorry'

cat > "$fixture_dir/string-adjacent-sorry.lean" <<'EOF'
#check sorry"not a raw string"
EOF
expect_rejected "$fixture_dir/string-adjacent-sorry.lean" 'forbidden proof mechanism: sorry'

for literal in 0 00 0_0 0x0 0X00 0x0_0 0b0 0B00 0b0_0 0o0 0O00 0o0_0; do
  fixture="$fixture_dir/zero-${literal}.lean"
  printf 'set_option maxHeartbeats %s in\nexample : True := by trivial\n' \
    "$literal" > "$fixture"
  expect_rejected "$fixture" 'unlimited maxHeartbeats'
done

cat > "$fixture_dir/comments-and-strings.lean" <<'EOF'
-- private axiom mentionedInComment : True
/- Nested comments may mention set_option
   maxHeartbeats 0 and /- sorry -/ safely. -/
def policyWords : String := "admit native_decide CertifiedArtifact"
def unicodeIdentifiers (βsorry sorryβ βsorryAx sorryAxβ : Nat) : Nat :=
  βsorry + sorryβ + βsorryAx + sorryAxβ
def interpolationText : String := s!"literal sorry; expression {"sorry"}"
#check m!"literal sorry; expression {"sorry"}"
#check f!"literal sorry; expression {"sorry"}"
macro "safePolicyProbe " message:interpolatedStr(term) : command =>
  `(command| #check $message)
safePolicyProbe "literal sorry; expression {"sorry"}"
def rawPolicyText : String := r###"sorry admit axiom " quoted"###
def suffixIdentifiers (sorry? sorry! sorryAx? sorryAx! : Nat) : Nat :=
  sorry? + sorry! + sorryAx? + sorryAx!
def subscriptIdentifiers (sorry₀ sorryAx₉ : Nat) : Nat := sorry₀ + sorryAx₉
def symbolIdentifiers (℘sorry sorry℘ ℘sorryAx sorryAx℘ : Nat) : Nat :=
  ℘sorry + sorry℘ + ℘sorryAx + sorryAx℘
set_option maxHeartbeats 1000 in
example : True := by trivial
EOF

python3 "$scanner" "$fixture_dir/comments-and-strings.lean"

for literal in 1 01 1_0 0x1 0X10 0x1_0 0b1 0B10 0b1_0 0o1 0O10 0o1_0; do
  fixture="$fixture_dir/nonzero-${literal}.lean"
  printf 'set_option maxHeartbeats %s in\nexample : True := by trivial\n' \
    "$literal" > "$fixture"
  python3 "$scanner" "$fixture"
done
printf 'Lean proof-policy scanner self-test: PASS\n'
