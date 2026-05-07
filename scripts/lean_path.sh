#!/usr/bin/env bash
# Source this from project scripts so a standard elan install works even when
# the parent shell has not added ~/.elan/bin to PATH.
if [[ -d "$HOME/.elan/bin" ]]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
