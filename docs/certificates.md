# Per-result certificate guide

`verify` closes the calculation-to-theorem path by having Lean independently check
the values proposed by Python. This avoids making correctness of Python's
recurrence an assumption of the numerical result. The application parser and
mapping to the displayed report remain explicit trusted components.

## Issue and recheck

After `make setup`, from the source project folder:

```sh
uv run --locked statproof verify examples/fixed_sample.toml \
  --control-successes 10 --treatment-successes 25 \
  --output .statproof/my-example
uv run --locked statproof check-certificate .statproof/my-example
```

The output directory must not exist, so a previous certificate cannot be silently
overwritten. Without `--output`, a unique directory is created under
`.statproof/certificates/`. The directory is ignored by Git. The JSON response gives
its absolute location and the certificate's content identifier.

Use `--project /path/to/statProof` when running from elsewhere. Verification needs
the Lean source project and its dependencies even if the Python CLI was installed
from a wheel. `--timeout` is a positive, finite number of seconds per backend
command, with default `120`. Verification can be expensive for large tables;
timeouts remain unresolved rather than falling back to unverified evidence.

## Properties checked

The generated `Proof.lean` contains explicit theorems for:

1. Positive declared arm sizes and observed counts within their bounds.
2. Support bounds equal to those of the formal hypergeometric definition.
3. The exact proposed p-value equal to the formal Fisher p-value.
4. The exact proposed observed table probability equal to the formal probability.
5. The reported decision equivalent to membership in the formal rejection event.
6. The general Type I error guarantee instantiated at the declared arm sizes.

Integer arithmetic uses factorial-based binomial coefficients whose equivalence
to the specification is proved in `StatProof/Computation.lean`. Cross-product
equalities certify proposed fractions, using Lean's kernel reduction. There is no
`native_decide` or native-evaluation axiom in the checked proofs.

Before declaring completion, the generated checker collects transitive assumptions
of all six theorems and permits only `propext`, `Classical.choice`, and `Quot.sound`.
The process must exit successfully and emit the input-specific audited completion
marker. A zero exit code by itself is insufficient.

## Bundle contents

| File | Purpose |
| --- | --- |
| `inputs.json` | Canonical declaration and exact result, including table and decision |
| `Proof.lean` | Human-reviewable statements and proofs for those exact inputs |
| `Proof.olean` | Compiled checked proof artifact |
| `transcript.log` | Build, environment, dependency, and Lean command transcript |
| `certificate.json` | Named claims, assumptions, trust boundary, versions, and hashes |

The input SHA-256 is computed from a deterministic JSON serialization of the
parsed declaration and result. It binds their semantics, rather than the original
TOML whitespace or comments. The certificate identifier is a deterministic digest
of the certificate fields excluding the identifier itself; creation time means
separate issuances can have different identifiers.

The certificate records the actual Lean version, pinned toolchain, dependency
revisions, and StatProof version. Dependency checkouts must match their pinned Git
revisions and have no local changes or untracked files. It records hashes of the
local Lean sources, application Python sources, Lake configuration/manifest, and
compiled project library. Source and artifact snapshots are checked again after
the proof to detect changes during verification.

## Replay and integrity

`check-certificate` validates the certificate digest and file manifest, reconstructs
all derived input/result fields, and regenerates the expected Lean statements. It
then requires the same source snapshot, toolchain pin, dependency pins, and module
version, rebuilds the local library, and reruns the proof and transitive audit.
It leaves the original bundle unchanged.

Current compiled project artifacts are checked for stability during replay. The
original compiled artifact hashes remain provenance records; replay's mathematical
evidence comes from rechecking the retained source against the bound definitions.
It does not infer proof validity from the old transcript or compiled artifact hash.

If source code changes after issuance, restore the bound source snapshot before
replaying that bundle, or issue a new certificate for the changed version. A
self-consistent set of modified hashes cannot make a false value pass: Lean still
has to prove the proposed value against the definitions.

The bundles are not digitally signed and do not establish authorship. Hashes bind
content and detect alterations; they do not authenticate the local installation
or the provenance of historical metadata. The local toolchain, imported artifacts,
statistical meaning of definitions, and application binding code are trusted.

## Assumptions and failures

The mathematical guarantee assumes independent binomial samples, positive sizes
fixed before outcomes, and the equal-proportions null. The supplied counts are
assumed to come from that declared procedure. Verification does not establish
that these real-world conditions hold, or certify power, coverage, or every
execution of the Python program.

Data-dependent stopping receives no fixed-sample certificate and no endorsed
procedure-level decision. Its justification remains unresolved; that does not
demonstrate inflated error.

An invalid proof, missing marker, dependency mismatch, changing sources/artifacts,
or backend timeout produces no `certificate.json`. The failed attempt may retain
its inputs, proof source, transcript, and `failure.json` for diagnosis. The report
remains `unresolved_obligation`, with `certificate_issued: false`. Malformed input
and existing output-directory errors use exit code `2`; incomplete verification
uses `1`; successful issuance or replay uses `0`.
