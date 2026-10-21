#!/usr/bin/env bash
set -euo pipefail
export MATHLIB_NO_CACHE_ON_UPDATE=1
cd "$(dirname "$0")/.."
# Materialize exactly the locked dependency sources before scanning FsFltz.
lake env true
# Fetch the pinned Mathlib closure actually imported by this library and its
# pinned FsFltz dependency. No dependency revisions are updated here.
mapfile -t modules < <(python3 - <<'PY'
from pathlib import Path
import re
files = list(Path('ClusterSkeleton').rglob('*.lean'))
files += list(Path('.lake/packages/fsfltz/FsFltz').rglob('*.lean'))
modules = set()
for path in files:
    for line in path.read_text().splitlines():
        match = re.match(r'^\s*import\s+(Mathlib(?:\.\w+)*)\s*$', line)
        if match:
            modules.add(match.group(1))
for name in sorted(modules):
    print(name)
PY
)
if ((${#modules[@]} == 0)); then
  echo 'No Mathlib imports found; refusing an empty cache request.' >&2
  exit 1
fi
lake exe cache get "${modules[@]}"
