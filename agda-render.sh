#!/usr/bin/env bash

# Note that this is incomplete as is because it needs

@agda@/bin/agda \
  --with-compiler=@ghc@/bin/ghci \
  --library-file=./libraries \
  --ignore-interfaces \
  --html \
  --html-dir=./html \
  --html-highlight=code \
  -W noMissingDefinitions
  -W noUnresolvedInteractionMetas \
  --allow-unsolved-metas \
  "$@"
