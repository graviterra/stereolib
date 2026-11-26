#!/usr/bin/env bash
# Run inside an aggregate memory-limited scope after both Lean fixtures have been built.
# Usage from the repository root: bash validation/ring-chronology/replay-centres.sh CHECKOUT GUAVA_JAR NEW_DIR
set -euo pipefail
checkout=$(realpath "${1:?Centres checkout}")
guava=$(realpath "${2:?Guava 13.0 jar}")
dest=$(realpath -m "${3:?fresh output directory}")
group=$(cut -d: -f3 /proc/self/cgroup)
limit=$(cat "/sys/fs/cgroup$group/memory.max")
[[ "$limit" =~ ^[0-9]+$ && "$limit" -le 6442450944 ]]
test "$(cat "/sys/fs/cgroup$group/memory.swap.max")" = 0
export LEAN_NUM_THREADS=1
exec 9>.cache/ring-build.lock
flock 9
mkdir "$dest"
mkdir "$dest/core" "$dest/classes"
commit=aaed608ee1d917fcd5f72964d9ca6227bd790804
probe=validation/ring-chronology
test "$(sha256sum "$guava" | cut -d' ' -f1)" = a82f12e66fe140d9180b67ba136cd5b236df77e8303f7efe29cdd20d66e740a5
git -C "$checkout" archive "$commit" core/src/main/java/com | tar -x -C "$dest/core"
lake env lean --run "$probe/ExportInputs.lean" > "$dest/frames.txt"
rg --files "$dest/core" -g '*.java' | sort > "$dest/sources.txt"
java -Xmx512m -jar "${ECJ_JAR:-/usr/share/java/eclipse-jdt-core-compiler-batch.jar}" -1.8 -proc:none -warn:none \
  -cp "$guava" -d "$dest/classes" @"$dest/sources.txt" "$probe/CentresProbe.java"
java -Xmx512m -cp "$dest/classes:$guava" CentresProbe "$dest/frames.txt" \
  > "$dest/reports.txt" 2> "$dest/diagnostics.txt"
# Labeller.label catches exceptions internally and writes the message to stderr.
if test -s "$dest/diagnostics.txt"; then cat "$dest/diagnostics.txt" >&2; exit 1; fi
diff -u "$probe/expected.txt" "$dest/reports.txt"
cat "$dest/reports.txt"
