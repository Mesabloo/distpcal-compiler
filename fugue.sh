#!/usr/bin/env bash

function join_by {
  local d=${1-} f=${2-}
  if shift 2; then
    printf %s "$f" "${@/#/$d}"
  fi
}

###################
##### OPTIONS #####
###################

DEBUG_OPTS=(
    "dump-dir:.fugue/debug"
    "dump-lex"
    "dump-parse"
    "dump-desugar"
    "dump-typecheck"
    "dump-computable"
    "dump-guarded"
    "dump-network"
    "dump-go"
)

FEATURE_OPTS=(
    # "no-color"
    # "no-progress"
)

WARN_OPTS=(

)

TARGET_OPTS=(
    "-t"
    "go"
    "-X"
    "go-pkg:main"
)


########################
##### COMMAND-LINE #####
########################

FUGUE=./.lake/build/bin/fugue

INCLUDES=(
    "$PWD/include"
)

# lake \
#   -R -KBUILD_TYPE=debug -KNO_CHECK_DOC \
#   exec fugue \
$FUGUE \
  compile \
  -d "$(join_by "," "${DEBUG_OPTS[@]}")" \
  -f "$(join_by "," "${FEATURE_OPTS[@]}")" \
  -W "$(join_by "," "${WARN_OPTS[@]}")" \
  -I "$(join_by "," "${INCLUDES[@]}")" \
  "${TARGET_OPTS[@]}" \
  "$@"
