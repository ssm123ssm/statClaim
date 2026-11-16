# Public fields and the Claims view

Language version `0.3.0` supports typed public fields on statistical objects and
execution results. See `examples/fields.stat` for the complete example.

```text
let level = analysis.alpha
let size = analysis.design.model.n_control
let verification = verify(typeI(analysis))
let status = verification.status
let evidence = verification.evidence
let certificate_file = evidence.certificate.file
```

Field syntax also works after calls: `verify(claim).status` creates one operation
and projects its eventual status. Projections, aliases, and lists do not rerun an
operation. Unknown fields have diagnostics at the exact field name. Only the
published schema is accessible; Python attributes/methods and internal storage
are not exposed. Dotted module imports keep their existing spelling.

## Field schema

| Object | Public fields |
| --- | --- |
| Model | `n_control`, `n_treatment` |
| Study design | `model`, `stopping` |
| Hypothesis | `model`, `predicate`, `value`, `statement` |
| Analysis | `design`, `null`, `alpha` |
| Family | `analyses`, `alpha`, `joint_law` |
| Observation | `analysis`, `control_successes`, `treatment_successes` |
| Claim | `kind`, `subject`, `scope`, `guarantee` (when the claim is one error bound) |
| Guarantee | `quantity`, `relation`, `bound`, `null`, `scope`, `sentence` |
| Verification result | `request_id`, `claim`, `source_sha256`, `status`, `diagnostics`, `evidence` |
| Calculation result | `request_id`, `claim`, `source_sha256`, `status`, `diagnostics`, `calculation`, `decision` |
| Evidence | `grade`, `sources`, `machine_checked`, `claim`, `certificate` (absent when cited), `references`, `established_properties`, `required_assumptions` |
| Certificate reference | `certificate_id`, `file`, `directory`, `sha256` |
| Calculation details | `p_value`, `alpha`, `observed_table_probability`, `p_value_le_alpha`, `test`, `test_version` |
| Diagnostic | `code`, `message`, `severity` |

The schema in `language_fields.py` is shared by elaboration, execution, field
completion, and hover. Static fields are reusable in statistical constructors:
`analysis.alpha` is an exact number that still undergoes the receiving
constructor's ordinary type/domain checks. Projecting a result's `claim` is also
possible before execution: this describes a proposition without establishing it.

## Optional evidence and execution phases

Other result fields depend on execution. Compilation preserves typed projections
rather than evaluating them. In fast JSON reports these are `DeferredValue`
records with `status: "not_executed"`, request ID, field path, and value type.
Pending evidence is **not** reported as absent evidence or as a successful proof.

`verification.evidence` has type `Option[Evidence]`. It contains checked evidence
only after successful verification and is absent after unmet requirements or
backend errors. **Field access through an optional receiver propagates absence**:
`verification.evidence.certificate.file` has type `Option[string]`. It produces a
path after success and no value after failure. Optional values serialize as the
actual value or JSON `null`; no implicit conversion to nonoptional evidence is
provided. An unsuccessful proof attempt does not disprove the claim.

Calculation details and the endorsed decision are also optional. For example,
`computation.calculation.p_value` returns an exact rational value after calculation,
without implying formal evidence. A numerical result can be available even when
the sampling requirements prevent endorsing a decision.

Execution-dependent fields may be named, aliased, projected further, or collected
in lists. They cannot yet configure statistical constructors: those inputs must
be known during compilation. A well-typed but deferred input reports
`runtime_dependency`; optional inputs are rejected where a nonoptional value is
required. This milestone does not introduce conditionals, optional unwrapping,
list indexing, or general constructor evaluation on runtime data.

```sh
uv run --locked statclaim compile examples/fields.stat --json
uv run --locked statclaim check examples/fields.stat --json
```

The first command checks fields/types without calculations, Lean, or artifacts.
The second resolves fields and retains named values in the ordinary execution
report, including evidence metadata and certificate references after success.

## Claims in VS Code

After reloading the extension development window, run **StatClaim: Show Claims**,
or expand **StatClaim Claims** in the Explorer. Open `examples/fields.stat` and
try completing `verification.` and `verification.evidence.`; hover shows types
and preserves optionality throughout the field chain.

The view follows the current `.stat` file and retains it while a certificate or
another non-statistical tab is open. It displays:

- Named claims and inline requested claims, with aliases grouped together.
- Their precise descriptions and declared assumptions.
- Known requirements, including those of a declared claim not yet requested for
  verification. Click a claim/requirement to reveal the source location.
- Planned operations with their result names. A clean plan is explicitly not a
  proof and supplies no checked evidence.
- Results from an explicit **StatClaim: Verify Current File** command whose
  editor version and source SHA-256 match the current document.

Successful verification exposes the certificate, established properties, and
**Required assumptions — not established by this proof**. These remain conditions
of the guarantee rather than facts proved about the real study. Clicking a
certificate opens its JSON file. Calculation results display the exact p-value
and decision, with an explicit statement that they supply no formal evidence.

After any edit, old results appear only under **Previous execution — stale**,
with the old version and SHA-256. They cannot supply evidence in the current
claim section. Server restarts invalidate current status too. Unsuccessful
checks show diagnostics and no evidence. Closing/reopening a source does not
restore a persisted proof status.

Claim inspection uses the custom read-only `statclaim/inspect` LSP request.
`language_inspection.py` supplies the same pure descriptions used by reports.
The request returns versioned compiler descriptions and requirements only; the
extension combines these with explicit execution reports. It never runs Lean
or calculations to populate the view.

See the [editor guide](editor.md) for setup, development launch, and test commands.
Python tests cover fields/staging/absence, private-field rejection, and pure
inspection. Node view-model tests cover stale versions/hashes, failed checks,
and mismatched claims. The real VS Code test exercises field completion, live
requirements, projected certificate fields, and current versus historical
evidence after and during edits and server restarts.
