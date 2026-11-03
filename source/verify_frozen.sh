#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd -- "$(dirname -- "$0")" && pwd)"
: "${AIM34_PINNED_ENV:?Set AIM34_PINNED_ENV to an already provisioned Lean/mathlib environment file}"
: "${AIM34_MATHLIB_ROOT:?Set AIM34_MATHLIB_ROOT to the pinned mathlib source repository}"
test "$(git -C "$AIM34_MATHLIB_ROOT" rev-parse HEAD)" = c44e0c8ee63ca166450922a373c7409c5d26b00b
RUN="$(mktemp -d "$HERE/replay_XXXXXXXX")"
mkdir -p "$RUN/logs"
python3 - "$HERE" "$RUN" <<'PY'
import sys,json,hashlib,pathlib,shutil
src,out=map(pathlib.Path,sys.argv[1:])
for r in json.loads((src/'source_manifest.json').read_text()):
 p=src/(r['module'].replace('.','/')+'.lean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'],str(p)
 q=out/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
review=src/'independent_review'
assert review.is_dir(), 'Independent review evidence is required; staging is not a release.'
for rel,digest in json.loads((review/'SHA256SUMS.json').read_text()).items():
 p=review/rel
 assert hashlib.sha256(p.read_bytes()).hexdigest()==digest,str(p)
for p in (review/'source').glob('*.lean'):
 shutil.copyfile(p,out/p.name)
PY
ulimit -v 4194304
unset LEAN_PATH
source "$AIM34_PINNED_ENV"
export LEAN_NUM_THREADS=1
export LEAN_PATH="$RUN:$LEAN_PATH"
cd "$RUN"
lean --version > logs/toolchain.txt
grep -q 'version 4.19.0' logs/toolchain.txt
for list in build_order.txt audit_modules.txt; do
  while IFS= read -r module; do
    test -n "$module" || continue
    echo "CHECK $module"
    set +e
    lean -j 1 -s 16384 -DElab.async=false -o "$module.olean" "$module.lean" > "logs/$module.log" 2>&1
    rc=$?
    set -e
    printf '%s\n' "$rc" > "logs/$module.exit"
    cat "logs/$module.log"
    test "$rc" -eq 0 || exit "$rc"
  done < "$HERE/$list"
done
echo "PASS frozen custom-source replay and independent semantic checks: $RUN"
