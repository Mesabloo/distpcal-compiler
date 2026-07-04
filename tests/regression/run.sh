#!/usr/bin/env bash
# Runs every tests/regression/{accept,reject}_*.tla file through the `fugue` CLI and checks
# the exit code matches what the filename promises (0 for accept_*, nonzero for reject_*).
#
# Scope note: right now this only exercises the pipeline through desugaring (Phase 5 and
# later aren't implemented yet), so an `accept_*.tla` passing here means "gets past
# desugaring," not "is a fully well-formed, type-correct program." As later passes (Phase 5
# well-formedness, Phase 6 type checking, …) land, some current `accept_*` files may start
# failing there for reasons unrelated to what they were originally written to test — that's
# expected, not a naming-scheme bug; such a file's purpose was always "exercises pass X,"
# and a later, unrelated pass rejecting it doesn't retroactively make pass X's behavior wrong.
# Revisit/split affected files if and when that happens, rather than assuming a regression.
set -uo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/../.." && pwd)"
fugue="$repo_root/.lake/build/bin/fugue"

# Only colorize on an actual terminal, and never if the user opted out via NO_COLOR
# (https://no-color.org) — matching this project's own `-fno-color` convention.
if [ -t 1 ] && [ -z "${NO_COLOR:-}" ]; then
  c_reset=$'\033[0m'
  c_bold=$'\033[1m'
  c_green=$'\033[32m'
  c_red=$'\033[31m'
  c_yellow=$'\033[33m'
else
  c_reset="" c_bold="" c_green="" c_red="" c_yellow=""
fi

if [ ! -x "$fugue" ]; then
  echo "${c_red}error:${c_reset} '$fugue' not found or not executable — run 'lake build' first." >&2
  exit 1
fi

pass_count=0
fail_count=0

for f in "$script_dir"/*.tla; do
  name="$(basename "$f")"
  case "$name" in
    accept_*) want_exit=0 ;;
    reject_*) want_exit=1 ;;
    *)
      echo "${c_yellow}SKIP${c_reset}  $name (name doesn't start with accept_ or reject_)"
      continue
      ;;
  esac

  "$fugue" -fno-color "$f" >/dev/null 2>&1
  got_exit=$?

  if { [ "$want_exit" -eq 0 ] && [ "$got_exit" -eq 0 ]; } || \
     { [ "$want_exit" -ne 0 ] && [ "$got_exit" -ne 0 ]; }; then
    echo "${c_green}PASS${c_reset}  $name"
    pass_count=$((pass_count + 1))
  else
    echo "${c_red}FAIL${c_reset}  $name (expected exit $want_exit, got $got_exit)"
    fail_count=$((fail_count + 1))
  fi
done

echo
if [ "$fail_count" -eq 0 ]; then
  echo "${c_bold}${c_green}$pass_count passed, $fail_count failed${c_reset}"
else
  echo "${c_bold}${c_red}$pass_count passed, $fail_count failed${c_reset}"
fi
[ "$fail_count" -eq 0 ]
