#!/usr/bin/env bash
# From the repository root, in a memory-bounded build scope:
# bash tools/centres10/setup.sh /path/to/centres /path/to/guava-13.0.jar
set -euo pipefail
checkout=$(realpath "${1:?Centres git checkout}")
guava=$(realpath "${2:?Guava 13.0 JAR}")
root=$(git rev-parse --show-toplevel)
cd "$root"
group=$(cut -d: -f3 /proc/self/cgroup)
limit=$(cat "/sys/fs/cgroup$group/memory.max")
[[ "$limit" =~ ^[0-9]+$ ]] || { echo "aggregate cgroup memory limit required" >&2; exit 1; }
mkdir -p .cache
exec 9>.cache/ring-build.lock
flock 9
commit=aaed608ee1d917fcd5f72964d9ca6227bd790804
printf '%s  %s\n' a82f12e66fe140d9180b67ba136cd5b236df77e8303f7efe29cdd20d66e740a5 "$guava" | sha256sum -c -
work=$(mktemp -d "$root/.cache/centres10-build.XXXXXXXX")
mkdir "$work/tree" "$work/classes"
git -C "$checkout" archive "$commit" core/src/main/java/com | tar -x -C "$work/tree"
mapfile -t sources < <(find "$work/tree" -name '*.java' | sort)
cp "$guava" "$work/guava.jar"
java -Xmx512m -jar /usr/share/java/eclipse-jdt-core-compiler-batch.jar -1.8 -proc:none -warn:none \
  -cp "$work/guava.jar" -d "$work/classes" "${sources[@]}" tools/centres10/Centres10.java
# Check the actual compiled release before making this installation active.
empty_report=$(printf 'centres-1.0\n' | /usr/bin/python3 -I tools/centres10/run_pinned.py "$work/classes:$work/guava.jar")
test "$empty_report" = '[]'
printf '%s\n' "$commit" > "$work/centres.commit"
sha256sum tools/centres10/Centres10.java > "$work/adapter.sha256"
ln -s "$work" "$work/link"
mv -Tf "$work/link" .cache/centres10
echo "Installed pinned Centres in $work"
