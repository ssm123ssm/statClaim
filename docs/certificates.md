# Certificate and replay guide

Every Lean certificate StatClaim issues is a certificate of a whole program,
`statclaim_program_certificate`. `statclaim check` builds one for each run that
verifies a claim; `statclaim report --lean` builds one on request. Replay either
with `check-certificate`.

```sh
uv run --locked statclaim check examples/fisher_result.stat --output .statclaim/my-run
uv run --locked statclaim check-certificate .statclaim/my-run/lean
```

## What it proves

The certificate's inputs are the source and the canonical program it compiles to.
Its proof, `Proof.lean`, is the program's translation to Lean
([proposal](proposals/lean-translation.md)):

- a definition for each declaration, and each contract fact Python checks,
  stated as a theorem Lean decides;
- the premises the claims rest on: the level of each cited or declared test, a
  graph's cited rule, and the level of an exact test inside a combination;
- one theorem per verified claim, and a final theorem that the premises imply
  every claim and can hold together.

Each claim's grade comes from the premises its proof uses: none is proved; only
members' premises, under a combination Lean proves, is conditional; its own cited
or declared premise is cited or declared. The certificate records each claim with
its grade and the line it comes from, and the grades must be the ones Lean's
dependencies give, when issued and on replay.

A claim whose proof Lean rejects is left out: the inputs name it, it stays
unresolved in the run, and the rest is built again in `lean-proved/`. An error in
the declarations themselves leaves every claim unresolved.

Before Lean prints its completion marker, which is bound to the inputs' SHA-256,
an audit checks that every contract fact, claim and the final theorem use no
axiom beyond `propext`, `Classical.choice` and `Quot.sound`. A zero exit code by
itself is insufficient. There is no `native_decide`.

## Bundle contents

| File | Purpose |
| --- | --- |
| `inputs.json` | The source, the canonical program, and any claims left out |
| `Proof.lean` | The translation and the audit, for review |
| `Proof.olean` | The compiled, checked proof |
| `transcript.log` | Build, environment, dependency and Lean transcript |
| `certificate.json` | Claims with their grades, premises, trust boundary, versions and hashes |

The output directory must not exist. Without `--output`, `check` creates one under
`.statclaim/programs/` and `report --lean` under `.statclaim/certificates/`. Use
`--project` to point at a checkout from elsewhere, and `--timeout` for seconds per
backend command.

## Replay and integrity

`check-certificate` checks the certificate's digest and file hashes, compiles the
source again and requires the same canonical program, translates it again and
requires the same `Proof.lean`, then reruns Lean with the same toolchain,
dependency pins and StatClaim version, and checks the grades again. It leaves the
bundle unchanged. A self-consistent set of rehashed files cannot pass: the proof
must be the one the inputs state, and Lean must check it.

Certificates of the earlier, per-claim kinds replay with the StatClaim version that
issued them.

The bundles are not signed and do not establish authorship. The local toolchain,
the statistical meaning of the Lean definitions, the translator's statements and
the application binding code are trusted; see the proposal's trusted base.

## Assumptions and failures

A certificate proves its claims for the study as declared, under the listed
premises and assumptions. It does not show that the real study meets them, and it
certifies no Python calculation beyond the values its claims state.

An invalid proof, a missing marker, a dependency mismatch, sources that change
during the check, or a timeout produces no `certificate.json`; the attempt keeps
its inputs, proof, transcript and `failure.json` for diagnosis, and the claims stay
unresolved.
