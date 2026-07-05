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
#
# Fixtures run in parallel (one `fugue` invocation per file, backgrounded, then `wait`ed on) —
# they're fully independent (each just reads its own file and exits), so there's no reason to
# pay for them one at a time. Each job prints its own PASS/FAIL line the moment it finishes,
# so output arrives as results come in rather than all at once at the end — meaning line order
# is now whatever order the jobs happen to finish in, not the fixed glob order the sequential
# version had. Each line is written with a single `echo` call (one `write()`, well under
# PIPE_BUF), so concurrent jobs' output doesn't interleave/corrupt mid-line. The final tally is
# still exact — each job also drops a one-word PASS/FAIL marker in a scratch directory, summed
# up after `wait`, not recomputed by re-parsing printed output.
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

results_dir="$(mktemp -d)"
trap 'rm -rf "$results_dir"' EXIT

names=()

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

  names+=("$name")

  (
    "$fugue" -f no-color,no-progress "$f" >/dev/null 2>&1
    got_exit=$?
    if { [ "$want_exit" -eq 0 ] && [ "$got_exit" -eq 0 ]; } || \
       { [ "$want_exit" -ne 0 ] && [ "$got_exit" -ne 0 ]; }; then
      echo "PASS" > "$results_dir/$name.status"
      echo "${c_green}PASS${c_reset}  $name"
    else
      echo "FAIL" > "$results_dir/$name.status"
      echo "${c_red}FAIL${c_reset}  $name (expected exit $want_exit, got $got_exit)"
    fi
  ) &
done

wait

pass_count=0
fail_count=0

for name in "${names[@]}"; do
  if [ "$(cat "$results_dir/$name.status")" = PASS ]; then
    pass_count=$((pass_count + 1))
  else
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
