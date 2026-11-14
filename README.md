# StatProof

A statistical design checker with a Python interface and a Lean 4 / Mathlib proof
backend. The [project brief](statistical_design_checker_project_brief.md) defines
the intended scope.

**Current state: environment and application scaffold. No statistical guarantee
has been proved, and no verification certificates are issued.** The Lean library
currently defines positive sample sizes and checks arithmetic facts about the
exact threshold `1/20`. The Python interface is not yet connected to Lean proofs.

## Development setup

Prerequisites: [uv](https://docs.astral.sh/uv/getting-started/installation/),
[elan](https://lean-lang.org/install/manual/), Git, and Make. Run from this folder:

```sh
make setup
uv run --locked statproof doctor
make check
```

Python 3.12 is selected by `.python-version`; `uv.lock` records Python dependency
versions. `uv sync` creates the local `.venv`. The existing system Python and
default Lean toolchain need not be changed. Lean and Mathlib are pinned to
`v4.35.0`; `lake-manifest.json` records exact dependency commits. First setup
downloads Lean, Mathlib sources, and the needed precompiled library files.

After the initial setup, use `uv sync --locked` and `lake build` for ordinary
development. Run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` deliberately when resolving or changing Lean
dependencies; review manifest changes. The `cache get` command in `make setup`
downloads only the imports needed by the initial scaffold. Add further imports
to that command as the formal library grows.

## Inspect the example declarations

```sh
uv run --locked statproof inspect examples/fixed_sample.toml
uv run --locked statproof inspect examples/data_dependent_stopping.toml
```

Both commands emit JSON planning reports with `unresolved_obligation`, empty
evidence, and `certificate_issued: false`. Exit code `1` means the obligation is
unresolved; malformed input uses exit code `2`. The second example additionally
explains why data-dependent stopping needs a separate justification. Neither
command invokes Lean or evaluates a statistical test. Unknown fields and
unsupported options are rejected rather than silently ignored.

## Layout

- `src/statproof/`: declaration parser and development CLI.
- `StatProof/`: Lean definitions and future statistical proofs.
- `examples/`: fixed-sample and modified-stopping declarations.
- `tests/`: input validation and checks against unsupported verification claims.
- `docs/development.md`: architecture boundaries and remaining milestone work.
- `.github/workflows/check.yml`: Python checks and Lean build for a future remote.

The repository is initialized locally; no remote or public release is configured.
A project license still needs to be selected before an open-source release.
