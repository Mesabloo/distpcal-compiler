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
    "dumpdir=.fugue"
    "dump-guarded"
    "dump-network"
)

TARGET_OPTS=(
    "--package"
    "main"
)


########################
##### COMMAND-LINE #####
########################

lake \
  -R -KBUILD_TYPE=debug -KNO_CHECK_DOC \
  exec fugue \
  -D "$(join_by "," "${DEBUG_OPTS[@]}")" \
  "${TARGET_OPTS[@]}" \
  "$@"
