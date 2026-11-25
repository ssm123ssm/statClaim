# Certificate and replay guide

Every Lean certificate StatClaim issues is a certificate of a whole program,
`statclaim_program_certificate`. `statclaim check` builds one for each run, even
one that only calculates; `statclaim report --lean` builds one on request. Replay
either with `check-certificate`. Calculated and simulated values are not proved.

```sh
uv run --locked statclaim check examples/fisher_result.stat --output .statclaim/my-run
uv run --locked statclaim check-certificate .statclaim/my-run/lean
```

## What it proves

The certificate's inputs are the source, the canonical program it compiles to,
and the values the run reports for each claim: a p-value and decision, an
interval, a selected sample size. `Proof.lean` writes the program and those values
as Lean data, adds numerical hints, and proves:

- `contracts`: every declared test and combination meets its contracts, and every
  claim has its shape, decided by `decide +kernel`;
- one theorem `program.Claim r` per claim that is ready, whose designs stop at fixed
  sizes, whose levels add up to at most each combination's own, and whose plan met
  its targets: the claim, as `StatClaim/Semantics` defines it, holds for every
  instance meeting the premises of the tests it involves. Each is proved by the
  soundness theorem, `Program.sound`, after the kernel checks the claim's hints. A
  wrong hint fails the build; it cannot change what is claimed.

The semantics covers Type I and familywise claims of exact, cited and declared
tests and their combinations (Bonferroni families, designs with looks, fixed
sequences and graphical procedures), results for observed data, intervals, and
planning claims ([proposals](proposals/lean-semantics.md)). A program that uses
something the semantics does not define gets no certificate, and the check says
what is missing. Blinded sample-size re-estimation stays outside Lean: its Type I
error is simulated.

Lean also prints the data's canonical form and each claim's grade. The canonical
form must be the certificate's program and reported values, and each grade the one
the certificate records, when issued and on replay. A grade is a Lean function of
the claim: proved, unless the claim rests on a member's premise under a
combination (conditional) or on its own cited or declared premise. A claim whose
design stops by a rule that depends on the data has no sampling law: the semantics
states it as false, and nothing proves it. A claim whose levels exceed their budget
stays unresolved, as Python leaves it. A run whose reported values differ from the
ones Lean checked loses the claim's evidence.

A claim whose proof Lean rejects is left out: the inputs name it, it stays
unresolved in the run, and the rest is built again in `lean-proved/`. An error in
the declarations themselves leaves every claim unresolved.

Before Lean prints its completion marker, which is bound to the inputs' SHA-256,
an audit checks that the contract facts and every claim use no axiom beyond
`propext`, `Classical.choice` and `Quot.sound`. A zero exit code by itself is
insufficient. There is no `native_decide`.

## Bundle contents

| File | Purpose |
| --- | --- |
| `inputs.json` | The source, the canonical program, the reported values, and any claims left out |
| `Proof.lean` | The program as Lean data, its hints, the theorems and the audit, for review |
| `Proof.olean` | The compiled, checked proof |
| `transcript.log` | Build, environment, dependency and Lean transcript |
| `certificate.json` | Claims with their grades, premises, trust boundary, versions and hashes |

The output directory must not exist. Without `--output`, `check` creates one under
`.statclaim/programs/` and `report --lean` under `.statclaim/certificates/`. Use
`--project` to point at a checkout from elsewhere, and `--timeout` for seconds per
backend command.

## Replay and integrity

`check-certificate` checks the certificate's digest and file hashes, compiles the
source again and requires the same canonical program, writes the Lean data and
hints again and requires the same `Proof.lean`, then reruns Lean with the same toolchain,
dependency pins and StatClaim version, and checks the grades again. It leaves the
bundle unchanged. A self-consistent set of rehashed files cannot pass: the proof
must be the one the inputs state, and Lean must check it.

Certificates of the earlier, per-claim kinds, and program certificates whose claims
the retired translator stated, replay with the StatClaim version that issued them.

The bundles are not signed and do not establish authorship. The local toolchain,
the statistical meaning of the Lean definitions and the semantics, the parser and
elaborator, Lean's JSON printer, and the application binding code are trusted;
see the proposals' trusted bases. The encoding is not: every build decides that
its program is in canonical form (`canonical`), and `Program.form_injective`
proves that two such programs never print the same form.

## Assumptions and failures

A certificate proves its claims for the study as declared, under the listed
premises and assumptions. It does not show that the real study meets them, and it
certifies no Python calculation beyond the values its claims state.

An invalid proof, a missing marker, a dependency mismatch, sources that change
during the check, or a timeout produces no `certificate.json`; the attempt keeps
its inputs, proof, transcript and `failure.json` for diagnosis, and the claims stay
unresolved.
