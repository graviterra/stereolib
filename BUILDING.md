# Building selected modules

Use the Lean version in `lean-toolchain` and the dependencies pinned in `lake-manifest.json`.
The project requires Python 3.11 or later for its build helper. Install the pinned Lean toolchain
with elan before building. Lake fetches dependencies when needed; this can require network access
and substantial time and memory on a fresh checkout.

Do not start an unrestricted whole-library build. A single target or `lake exe` can still build
a large dependency graph. Every build must run inside an enforced aggregate memory limit covering
Lake, Lean, compilers, linkers, and all descendants. One compiler thread or a per-process `ulimit`
does not provide that protection.

First inspect the selected module's local dependency plan. This command does not run Lean:

```sh
python3 -B tools/build_lean_project_bounded.py --check \
  --module TetraStereo.OneCenter.Geometry
```

On Linux with a working user systemd manager and cgroup memory controller, a bounded build is:

```sh
systemd-run --user --scope \
  --property=MemoryMax=6G --property=MemorySwapMax=0 \
  --property=RuntimeMaxSec=30min \
  python3 -B tools/build_lean_project_bounded.py \
    --module TetraStereo.OneCenter.Geometry
```

Confirm that the host enforces these properties, and choose a limit leaving memory for the OS
and other applications. Use an equivalently constrained container or batch job on other hosts;
do not fall back to an unrestricted build if the memory controller is unavailable.
The helper serializes local-module builds. Its name does not mean it imposes a memory limit.
Its execution mode requires an explicit `--module` or `--through-module` selection.
External dependency builds may still run concurrently within the enforced scope.

Repeat `--module` to select multiple endpoints. `--through-module` instead selects a topological
prefix and can include unrelated modules. Keep `.lake/` for incremental builds. The helper's
progress cache is a build optimization, not proof certification.

Some demonstration modules execute computations and write generated files during elaboration.
They are included as source, but are not added to the umbrella merely because they exist.
Select such modules deliberately and run them inside the same resource limits.

For static verification only:

```sh
python3 -B tools/check_source_tree.py
python3 -B -m unittest discover -s tests
```

These commands do not launch Lean. This source distribution has not yet undergone a full
clean-checkout build, and a green static CI result does not establish that such a build passes.
