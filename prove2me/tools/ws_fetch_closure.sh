#!/bin/bash
# Fetch the missing Mathlib oleans of the workspace's import closure from the Mathlib cache, in
# batches, dropping the downloaded archives, the C output and the editor index after each batch so
# the session's disk allowance holds.  The cache ships .olean, .olean.private, .olean.server, .ir and
# .ir.sig: nothing else must be deleted (deleting the parts forces a recompile from source; deleting
# anything Lake tracks makes a later `lake build` rebuild Mathlib).  Stops below 250 MB free.
# Usage: P2M_DIR=<dir> prove2me/tools/ws_fetch_closure.sh <list of .lake/packages/mathlib/Mathlib/**.lean paths>
set -u
S=${P2M_DIR:?set P2M_DIR}
LIST=${1:?list file}
export PATH=$S/toolchain/bin:$PATH
cd $S/ws
total=$(wc -l < $LIST); n=0; batch=150
while [ $n -lt $total ]; do
  free_kb=$(df --output=avail $S | tail -1)
  if [ "$free_kb" -lt 256000 ]; then echo "STOP: only $((free_kb/1024)) MB free after $n files"; exit 2; fi
  files=$(sed -n "$((n+1)),$((n+batch))p" $LIST | tr '\n' ' ')
  lake exe cache get! $files > $S/fetch_batch.log 2>&1; rc=$?
  rm -rf /root/.cache/mathlib/* .lake/packages/mathlib/.lake/build/ir
  find .lake/packages/mathlib/.lake/build/lib/lean -name '*.ilean' -delete
  n=$((n+batch))
  echo "batch to $n/$total: rc=$rc $(grep -o 'Decompressed [0-9]* file' $S/fetch_batch.log | tail -1); free $(( $(df --output=avail $S | tail -1) / 1024 )) MB"
done
have=0; while read f; do m=${f#.lake/packages/mathlib/}; m=${m%.lean}; [ -f .lake/packages/mathlib/.lake/build/lib/lean/$m.olean ] && have=$((have+1)); done < $LIST
echo "DONE: $have of $total oleans present (the rest have no cache entry and are compiled from source by compile_modules.py)"
