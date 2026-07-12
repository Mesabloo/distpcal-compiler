#!/usr/bin/env bash
# Runs every tests/regression/{accept,reject}_*.tla file through the `fugue` CLI and checks
# the exit code matches what the filename promises (0 for accept_*, nonzero for reject_*).
# A `skip_*.tla` file is never run at all — reported as a yellow SKIP and excluded from the
# pass/fail tally — for a fixture that's known-broken or deferred right now (e.g. exercises a
# parser/pass gap tracked elsewhere) without deleting it or miscounting it as a failure.
#
# Scope note: an `accept_*.tla` passing here only means "gets past whatever pipeline stages
# are currently wired into the CLI," not "is a fully well-formed, type-correct program." As
# new passes land, some current `accept_*` files may start failing there for reasons unrelated
# to what they were originally written to test — that's expected, not a naming-scheme bug;
# such a file's purpose was always "exercises pass X," and a later, unrelated pass rejecting it
# doesn't retroactively make pass X's behavior wrong. Revisit/split affected files if and when
# that happens, rather than assuming a regression.
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
cleanup() {
  if [ "${fail_count:-0}" -eq 0 ]; then
    rm -rf "$results_dir"
  fi
}
trap cleanup EXIT

# `time`'s builtin report, not an external `date +%N`/`perl` dependency — macOS's stock `date`
# has no sub-second resolution, this works on any bash. `%R` = wall-clock seconds, "0.042" style.
TIMEFORMAT='%R'

names=()
skip_count=0

for f in "$script_dir"/*.tla; do
  name="$(basename "$f")"
  case "$name" in
    accept_*) want_exit=0 ;;
    reject_*) want_exit=1 ;;
    skip_*)
      echo "${c_yellow}SKIP${c_reset}  $name"
      skip_count=$((skip_count + 1))
      continue
      ;;
    *)
      echo "${c_yellow}SKIP${c_reset}  $name (name doesn't start with accept_/reject_/skip_)"
      skip_count=$((skip_count + 1))
      continue
      ;;
  esac

  names+=("$name")

  (
    log="$results_dir/$name.log"
    timefile="$results_dir/$name.time"
    { time "$fugue" -f no-color,no-progress "$f" >"$log" 2>>"$log"; } 2>"$timefile"
    got_exit=$?
    elapsed="$(cat "$timefile")"
    rm -f "$timefile"
    if { [ "$want_exit" -eq 0 ] && [ "$got_exit" -eq 0 ]; } || \
       { [ "$want_exit" -ne 0 ] && [ "$got_exit" -ne 0 ]; }; then
      echo "PASS" > "$results_dir/$name.status"
      rm -f "$log"
      echo "${c_green}PASS${c_reset}  $name (${elapsed}s)"
    else
      echo "FAIL" > "$results_dir/$name.status"
      # Built as one string and printed with a single `echo` (one `write()`) rather than piping
      # through `sed` line-by-line — same interleaving concern as the PASS/FAIL line itself
      # (see file header): two failing jobs' prefixed logs could otherwise interleave mid-line.
      prefixed="$(sed 's/^/> /' "$log")"
      echo "${c_red}FAIL${c_reset}  $name (expected exit $want_exit, got $got_exit, ${elapsed}s) — log: $log
$prefixed"
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
  echo "${c_bold}${c_green}$pass_count passed, $fail_count failed, $skip_count skipped${c_reset}"
else
  echo "${c_bold}${c_red}$pass_count passed, $fail_count failed, $skip_count skipped${c_reset}"
  echo "Failing tests' full output kept at: $results_dir"
fi
[ "$fail_count" -eq 0 ]
