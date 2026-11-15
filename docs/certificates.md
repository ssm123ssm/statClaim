# Certificate and replay guide

The standalone file language uses these same certificate kinds and proof
generators. `statproof check examples/fisher.stat --output .statproof/my-program`
retains the source and typed program in a parent run directory, then places each
verified request's certificate in `request-NNN/`. Replay that request directory
with `check-certificate`. The parent `run.json` is a source/IR provenance report,
not a mathematical certificate. Translation from `.stat` declarations remains a
trusted application boundary. See the [file-language guide](stat-language.md).

Planning claims issue `statproof_planning_certificate` (a fixed design's Type I
bound and its power at one point) and `statproof_policy_certificate` (a complete
single-arm design). `statproof_binomial_result_certificate` covers an observed
one-sample result. All replay with `check-certificate`.

Design and family workflows need no observations. Fisher's alpha is configurable
as an exact string in the optional `[analysis]` table; it defaults to `1/20`.
The bound in the generated proof and certificate uses that declared value.

The primary design workflow is:

```sh
uv run --locked statproof verify-design examples/fixed_sample.toml \
  --output .statproof/my-design
uv run --locked statproof check-certificate .statproof/my-design
```

`verify-design` constructs the declared model, fixed sampling plan, and Fisher
analysis through the shared Lean objects. It checks positive sizes, the fixed
plan, the sampling compatibility contract, the core design claim, and the uniform
Type I error bound at the declared alpha for every common success probability in `[0, 1]`.

The resulting `statproof_design_certificate` has `verification_scope: "design"`
in its report and no calculation or decision. Its inputs contain the design,
procedure identifier/version, equal-proportions null, and the exact chosen threshold.
It certifies only the named design properties under explicit assumptions.

`verify-family` issues a third kind, `statproof_family_certificate`, with
`verification_scope: "family"` in its report. It composes the declared Fisher analyses
using the generic Bonferroni theorem. Its retained proof quantifies over all
joint sampling-law families satisfying the explicitly declared binomial marginal
contracts and all joint parameters, including mixed true/false nulls. No
independence between outcomes is assumed. The sum of the exact allocated
levels must be at most the requested family bound. Every sampling plan must be
fixed for this adapter. See the [multiple-testing guide](multiple-testing.md).

Observed data and execution correctness are a separate, optional workflow.

`verify-result` (or its original name, `verify`) closes the calculation-to-theorem
path by having Lean independently check the values proposed by Python. This avoids making correctness of Python's
recurrence an assumption of the numerical result. The application parser and
mapping to the displayed report remain explicit trusted components.

## Issue and recheck

After `make setup`, from the source project folder:

```sh
uv run --locked statproof verify-result examples/fixed_sample.toml \
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

Each mode emits its own set of explicit theorems in `Proof.lean`. Family
certificates check positive sizes, the allocation inequality, conditional marginal
Fisher bounds, and the strong familywise claim. They retain the assumed
marginal-law equalities as explicit hypotheses of the theorem. Design-only
certificates verify the declarations and general guarantee, without any supplied
counts or numerical results. Per-result certificates (`statproof_per_result_certificate`)
add the following checks:

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
of all theorems required for the selected mode and permits only `propext`,
`Classical.choice`, and `Quot.sound`.
The process must exit successfully and emit the input-specific audited completion
marker. A zero exit code by itself is insufficient.

## Bundle contents

| File | Purpose |
| --- | --- |
| `inputs.json` | Canonical design and analysis; additionally the exact result for per-result certificates |
| `Proof.lean` | Human-reviewable statements and proofs for those exact inputs |
| `Proof.olean` | Compiled checked proof artifact |
| `transcript.log` | Build, environment, dependency, and Lean command transcript |
| `certificate.json` | Named claims, assumptions, trust boundary, versions, and hashes |

The input SHA-256 is computed from a deterministic JSON serialization of the
parsed design request, or the declaration and result for a per-result check. It
binds their semantics, rather than the original TOML whitespace or comments.
The certificate identifier is a deterministic digest
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

Replay selects a fixed scope from the certificate kind and validates its claims,
assumptions, theorem names, and canonical inputs against that scope. A design
certificate cannot be promoted to evidence about an observed result by changing
its metadata or recomputing hashes.

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

The mathematical guarantee assumes independent binomial samples and positive
sizes fixed before outcomes. It bounds error under the equal-proportions null,
without asserting the null is true for a real study. For per-result certificates,
the supplied counts are additionally assumed to come from that declared procedure.
Verification does not establish
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
