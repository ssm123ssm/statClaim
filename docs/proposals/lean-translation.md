# Proposal: translating StatClaim programs to Lean

Status: approved 2026-11-23; in progress.

Progress:

- Milestone 1 done: `src/statclaim/lean_translation/table.py` classifies every
  constructor and operation, checked by `tests/test_lean_translation.py`.
- Milestone 2 done: `StatClaim/Interface/` (`Outcomes`, `Premises`, `Program`)
  and `StatClaim/Generated/Methods.lean`, written from the registry by
  `scripts/update_lean_premises.py`; checked by `tests/lean/Interface.lean` and
  `tests/test_lean_translation.py`.
- Milestone 3, part 1 done: `lean_translation/program.py` translates two-arm
  models, fixed and unspecified sampling plans, nulls, cited and declared trial
  tests, the two-sided Fisher test and their Type I claims. All 112 corpus
  programs the compiler accepts translate and Lean accepts them, 33 claims in
  all; everything not yet translated is listed with its reason.
  `scripts/check_lean_translation.py` runs in `make lean-check`, and a Lean test
  confirms that breaking a contract or overstating a claim is rejected.
- Milestone 3, part 2 done: observational studies as abstract models
  (`ObservationalModel`, with no association as a zero association), and the
  cited tests of association with their registry contracts: design, scales,
  survey, minimum total, clusters and covariates. 41 claims in all. The remaining
  exact tests (one-sided Fisher, the margin test, randomisation, one-sample,
  two-stage, and the exact tests of association) move to milestone 5: each needs
  its numerical certificate, and the association module first needs a bridge to
  the core objects.

## Goal

Every `.stat` program translates to a Lean file whose final theorem states that
the program's claims, and the compatibility of its declarations, follow from a
listed set of premises. Cited and declared guarantees enter as named premises,
never as axioms. One general translator replaces the per-claim proof templates,
and the existing corpus of `.stat` files tests it against the Python compiler.

## Where we are

- **Python** checks types and contracts while compiling
  (`language_contracts.py`), explains them (`derivations.py`) and re-checks the
  explanations independently (`derivation_checker.py`).
- **Lean** holds the core objects (`StatClaim/Core/Objects.lean`: `Model`,
  `SamplingPlan`, `Compatibility`, `Analysis`, `Claim`, `Certificate`, `Module`;
  `Core/Policy.lean` for stopping rules) and one module per exact method.
- **The bridge** is 30 hand-written templates in 8 Python files. Each fills
  numbers into a fixed Lean file that applies one named theorem to one kind of
  claim.

This has three costs. Contracts and theorems are maintained separately, so
only tests and review keep them in agreement. Each new claim kind needs a new
template. A program without `verify` gets no Lean evidence at all, even for
facts Lean could decide at once.

## Principles

1. **Assumptions are hypotheses, never axioms.** A false premise makes its own
   conclusion empty; a false axiom could make everything provable. The axiom
   audit (`propext`, `Classical.choice`, `Quot.sound` only) stays.
2. **Lean is the authority at check time; Python is the fast path.** Python
   still elaborates every program and checks its contracts, because Lean can
   only receive programs that elaborate, and it keeps giving instant
   diagnostics in the editor and both studios. Lean decides at `check` and
   `report`, and tests require the two to agree. See
   [roles after translation](#roles-after-translation).
3. **One source of truth.** The Lean premises are generated from the Python
   method registry, as `docs/catalogue.md` is.
4. **Coverage is explicit.** Every constructor either has a Lean translation or
   states why not. Nothing is left out silently.
5. **Grades come from premises.** A claim's grade follows from the premises left
   in its theorem, not from a label assigned in Python.
6. **Migration never weakens a certificate.** A template is retired only after
   the new theorem is proved to imply the template's statement.

## Part 1: the Lean library

### Layout

- `StatClaim/Core/`, `StatClaim/Modules/`: unchanged.
- `StatClaim/Interface/`: new, hand-written. Abstract models, tests, premises
  and the shape of a program theorem.
- `StatClaim/Generated/Methods.lean`: new, generated from the registry. One
  entry per cited method.

### Level A: interface premises, for every method

A test is seen from outside: a measurable rejection event, and a premise about
its level. Sketch, not final code:

```lean
/-- A test seen from outside: the outcomes on which it rejects. -/
structure TestInterface (Outcome : Type) [MeasurableSpace Outcome] where
  reject : Set Outcome
  measurable : MeasurableSet reject

/-- The level premise. A finite-sample guarantee has slack 0. A large-sample
guarantee has an unknown slack that is carried into every conclusion, so it is
never reported as a bound at the level. -/
def LevelPremise (law : Parameter → Measure Outcome) (null : Parameter → Prop)
    (test : TestInterface Outcome) (α : ℚ) (slack : ℝ) : Prop :=
  0 ≤ slack ∧ ∀ θ, null θ → (law θ).real test.reject ≤ α + slack
```

`Composition.familywise_le` already works this way, with abstract rejection
sets and slack terms, so Level A is enough for:

- contract fit: model identity, supported null form, direction, margin, level;
- composition: Bonferroni, fixed sequence, interim looks, graphical procedures;
- grades.

**Models without a Lean law.** For continuous and survival outcomes, the
program theorem quantifies over every model of the declared outcome type, with
an `effect : Parameter → ℝ` on which null forms are predicates
(`equal_means` is `effect θ = 0`; `mean_difference_at_most v` is
`effect θ ≤ v`). The claims then hold for any law that satisfies the premises.
Analyses that share an assignment share the quantified model. The exact
binomial and observational modules keep their concrete laws.

**Generation.** `scripts/update_lean_premises.py` reads `methods.METHODS` (11
trial methods), `methods.OBSERVATIONAL` (10 observational methods) and the null
forms in `methods.NULL_FORMS`, and writes `StatClaim/Generated/Methods.lean`.
Each entry has the method's key, version, grade, scope, supported null forms
and assumption ids, with the guarantee sentence as its doc comment. `--check`
runs in CI, like `catalogue-check`, so a method change without regeneration
fails. A declared test's premise is generated per declaration in the program,
from the method and reference the author supplies.

### Level B: defined premises, only where needed

For a chosen method, the law and the statistic are defined in Lean by hand: for
example a normal two-sample law and the pooled t statistic. The premise becomes
a precise statement that a later proof could discharge. This is formalisation
that needs statistical review, so it is done one method at a time, only for
methods that are candidates for a proof. The pooled t-test under normality is
the natural first candidate. Every other method stays at Level A.

## Part 2: the translator

### Input and output

The input is the compiled program: its typed objects, with their canonical
JSON form (`language.normalize`, the form certificates already bind) deciding
when two values are the same. The Python contracts compare models by value, so
two identical declarations become one Lean definition. The translator never
reads source text, so names are resolved and types checked before it runs.
Nested values in the canonical JSON carry no type, so the translator dispatches
on the typed objects rather than on JSON shapes.

The output is one Lean file per program. Sketch:

```lean
import StatClaim
namespace StatClaimProgram   -- one namespace per program

-- one definition per `let`, in dependency order
def study := ...
def analysis := ...

-- contract facts the Python compiler checks, decided by Lean
theorem contracts : <facts> := by decide

-- every premise the claims rest on, named after method, version and assumption
structure Premises where
  t_test_level : LevelPremise ...

-- the stated claims, or compatibility alone when there are none
theorem claims (premises : Premises) : <claim₁> ∧ <claim₂> := ...

-- the premises can hold together, so `claims` is not vacuous
theorem premises_satisfiable : ∃ instance, Premises instance := ...
end StatClaimProgram
```

The satisfiability witness rules out contradictory premises, under which
`claims` would hold trivially. For interface premises it is cheap: a test that
never rejects meets every level premise. It does not show that the premises
hold for the study's actual tests.

### The table

`src/statclaim/lean_translation/` holds:

- `table.py`: every constructor in `language.MODULES` and every operation in
  `language.OPERATIONS`, mapped to an emitter or to "not in Lean" with a
  reason. Searches, calculations, simulations and precision targets are "not
  in Lean: calculated or simulated".
- `emit.py`: Lean text with stable names, exact rationals and escaping.
- `program.py`: walks the bindings in dependency order, collects each
  emitter's definition, decidable facts and premises, and writes the file.

An emitter receives one compiled value and returns a Lean term, the decidable
facts it requires and the premises it introduces. A single claim is proved
directly, from its premise or from its module's existing theorem. From
milestone 4, compositions are proved by a StatClaim tactic that searches the
library's composition lemmas; see [proof search](#proof-search). Emitters then
state goals rather than assemble proofs.

### Grades from premises

For each claim, the premises its proof term actually depends on determine the
grade, not the premises the translator meant it to use. Premises are fields of
the generated `Premises` structure, so a proof that uses one contains its
projection as a named constant; a collector built like the axiom audit lists
them per claim:

| Premises left | Grade |
| --- | --- |
| None | proved |
| Members' level premises, under a proved combination | conditional |
| The claim's own cited premise | cited |
| A declared premise | declared |

### Trust

The translator decides what each declaration means in Lean, so it is trusted
code (see [trusted base](#trusted-base)). It is kept small and table-driven, and each certificate keeps the
canonical input so the translation can be audited. A later step can move the
decidable contract checks into Lean itself: the program as a Lean data type, a
checker written in Lean and proved sound once, and each check a computation the
kernel trusts.

## Proof search

Single claims are proved directly, and the heavy numerical certificates stay
explicit. Compositions are where hand-assembled proofs would multiply, so from
milestone 4 a StatClaim tactic finds them.

**The hybrid.** Python states each claim's goal and may name lemmas worth
trying. A `statclaim` tactic, an `aesop` rule set (Aesop ships with Mathlib)
together with `decide`, `norm_num` and `simp`, finds a proof from the program's
premises, the module theorems and the composition lemmas tagged with a
`@[statclaim]` attribute. A new composition rule is then one tagged lemma, a
table entry and an emitter that states its goal; it needs no proof code in
Python.

**What search does.** It applies composition lemmas recursively, so a fixed
sequence containing a graph containing a family needs no special case. It
matches each member's guarantee to a premise or a module theorem, and it
discharges side conditions: levels summing to at most the family level, a null
form a method supports, sizes above a method's minimum.

**What stays explicit.** Exact power sums, the failure of each smaller candidate
in a search and other checks by kernel computation stay as today, split per
candidate. Generic search over them would exhaust memory, as a single proof over
all candidates once did. Search cannot discover a statistical theorem the
library lacks; it only connects theorems that exist.

**Guardrails.**

- The kernel stays the only judge. `native_decide` stays out; the axiom audit
  already rejects the extra axiom it adds.
- Each claim is its own theorem, with a fixed heartbeat budget, so a failure
  names the claim or member that failed.
- A search that fails or exhausts its budget leaves the claim unresolved and
  says so. That differs from a contract fact that `decide` evaluates to false,
  which is a violation; reports keep the two apart.
- Grades come from the dependency collector, never from how a proof was found,
  so a proof that uses a cited premise cannot be reported as proved.
- The corpus build time is tracked. A claim kind for which search proves too
  slow can return to an explicit proof from its emitter.

**Effect on trust.** Proof assembly was already untrusted, since the kernel
checks it; moving it from Python into a Lean tactic leaves soundness unchanged.
The dependency collector is new trusted code, because it decides grades. It is
small and tested exhaustively with proofs that use and avoid each kind of
premise.

## Roles after translation

Python checks contracts while it elaborates, not afterwards: `elaborate.py`
runs each constructor's contract as the constructor is applied, and a
declaration that fails produces no typed object. `language_compiler.requirements`
then adds open requirements for the requested claims. Translation does not
change this order; it adds a second stage.

```text
keystroke → parse → elaborate with contracts → requirements → live diagnostics
                                                               (milliseconds)
check     → canonical JSON → translator → Lean build → certificate
            (only for programs that elaborate)          (seconds)
                                                       → results mapped to source
```

**Python keeps** elaboration and contract checks, as the first gate; live
diagnostics with source spans, related locations and fix suggestions; the
studio's hints, which work by building constructors with a value; readable
explanations (`derivations.py`); and calculations and simulations. These must
run per keystroke, in the web studio and without Lean.

**Lean takes** the authority over compatibility and claims at `check` time.
One build per program gives both the compatibility certificate and the proofs.
For Lean-backed claims it replaces `derivation_checker.py`, since the kernel
does that job.

**Disagreement is a defect.** If Python accepts a declaration and Lean cannot
establish its compatibility, the check fails with an error naming both. It is
never shown as a weaker status.

**Two diagnostic channels.** Python's diagnostics stay the live channel. Lean's
outcomes arrive like `verify` results today: the translator records which Lean
name came from which declaration, so each outcome attaches to its source line,
in the Claims view and the studio's result trays, tied to a document version and
marked outdated after an edit. Lean runs on `check`, or optionally in the
background after saving where it is installed, never per keystroke.

**Later, if needed.** The rules already exist as data in `derivations.RULES`. One
declarative rule table could generate both the Python checks and the Lean
`Requires` propositions. The differential tests give the same protection with
less machinery, so this waits until divergence is a real cost.

## What it lets us claim

Accurate after translation:

- An audited Lean build of the generated file proves that, for the declared
  model, if the listed premises hold, then the program's declarations are
  compatible and its claims follow, as these are defined in the StatClaim Lean
  library.
- **Audited build** means more than an exit status of 0: the file contains no
  `sorry`, its theorems depend on no axiom beyond `propext`, `Classical.choice`
  and `Quot.sound`, and it prints the completion marker bound to that exact
  canonical input, so a stale compiled file cannot pass. The certificate
  pipeline already enforces this for `verify`.
- For each program, StatClaim generates a Lean theorem whose type states that
  the listed premises imply the compatibility of its declarations and its
  claims. Lean's kernel checks a proof term of that type.
- Under the propositions-as-types reading of Curry–Howard, each certificate is
  a term of that type. Premises are the theorem's hypotheses, the arguments of
  that term, not axioms.

Not accurate, and not to be claimed:

- **The `.stat` language is not dependently typed.** Its types are nominal and
  its contracts are checks run during elaboration. The direction agreed in
  2026-11 is to describe this as assume-guarantee reasoning, and translation
  does not change the surface language.
- **The translation is trusted, not verified.** The meaning of a program in Lean
  is whatever the translator emits.
- **Rejections are not refutations.** A program Python rejects never reaches
  Lean, so no Lean proof shows it is incompatible, unless a module proves a
  specific impossibility, as `no_compatibility_without_law` does.
- **Proofs are not programs.** The library uses classical reasoning
  (`Classical.choice`) and non-computable measures, so the proofs-as-programs
  reading of Curry–Howard does not apply. Propositions-as-types does.

Stronger statements need stronger designs. A checker written in Lean and proved
sound against a Lean semantics of the program would let the decidable contract
checks be called proved sound. Writing the language itself as Lean syntax with
its own elaborator would make it a dependently typed embedded language, at the
cost of the Python editor, studios and package.

## Trusted base

The rule: trusted code decides what is stated; untrusted code only produces
proofs, which Lean checks. A bug in untrusted code makes a build fail. A bug in
trusted code can make a proof of the wrong statement pass.

Trusted, kept small and reviewed line by line:

| Part | Where | Why it is trusted | How it is kept honest |
| --- | --- | --- | --- |
| Lean kernel and Mathlib | `lean-toolchain`, `lake-manifest.json` | They check every proof | Pinned versions |
| Definitions behind statements | `StatClaim/Core/`, and the definitions (not the proofs) in `StatClaim/Modules/`: laws, rejection events, policies, null predicates, claim propositions | They fix what every theorem means | Statistical and formal review |
| Interface library | `StatClaim/Interface/` | `LevelPremise`, its slack and the program-theorem shape: one wrong inequality empties every cited composition | Size budget, review, instances checked in known cases |
| Premise data and generator | The registry fields that state guarantees (relation, scope, bound, null form), `scripts/update_lean_premises.py`, `StatClaim/Generated/Methods.lean` | They decide what each cited guarantee says in Lean | Method version fixture, `--check`, reviewed diffs of the generated file |
| Translator denotation | `lean_translation/table.py`: the Lean term each declaration denotes and the proposition each claim becomes | A wrong entry gives a proof of the wrong statement | Table-driven, golden files, template equivalence |
| Values from source | The parser, elaboration of values and `language.normalize` | The statement must be about the study the source describes | Source and canonical input kept in each certificate; readings show each value in words; round-trip tests |
| Grade from premises | One function, and the dependency collector that lists the premises each claim's proof uses | Together they decide the evidence grade shown | Exhaustive tests over premise kinds, with proofs that use and avoid each one |
| Certificate checks | The audit, completion marker, input binding and replay in `verification.py` | They decide whether a build counts | Existing tests, including tampered bundles |
| Result binding | The translator's map from Lean names to declarations, and the report | A proof must be shown against the claim it proves | A test that every result maps to its own declaration |

Not trusted: a bug here causes a failed build, a missed result or a poor
message, never a false certificate.

- Proofs in the Lean library, the emitters' proof assembly, and the
  `statclaim` tactic with its lemma sets.
- Python contracts once Lean is the authority, and the explanations in
  `derivations.py`.
- Calculations and simulations, which never carry evidence.
- The language server, studios and command-line rendering, apart from result
  binding.

Rules:

1. Statement and proof live apart. In the translator, denotation and proof
   assembly are separate files.
2. In Lean, definitions stay few and plain; proofs may be as long as needed.
3. A change to a trusted path needs statistical and formal review. The paths
   are listed in `CONTRIBUTING.md`, or in a `CODEOWNERS` file, so a review is
   not missed.
4. Each milestone reports the size of the trusted code. It should grow slowly,
   while proofs grow freely.

The values-from-source row is the hardest to keep small: the parser and
elaborator are thousands of lines. It is trusted only for building values
faithfully, not for checking contracts, and the certificate's canonical input
lets a reviewer see exactly which study a proof is about.

## Part 3: testing on the existing corpus

The corpus is every file in `examples/` (examples, tutorial and article
programs) and `replication/*/` (115 files), the 43 error-injection scenarios in
`replication/scenarios.py`, and optionally the designs the studio wizard
generates.

1. **Translation is total.** Every corpus file translates, or names its parts
   that are not in Lean, without an error. Python only, in `pytest`.
2. **Validity agrees.** All translated programs build in one Lean build, one
   namespace each, so Mathlib is imported once. A file the compiler accepts
   must typecheck. Runs in a Lean CI shard.
3. **Rejection agrees.** A file the compiler rejects, or leaves with an open
   requirement, must fail in Lean or leave the matching premise unproved. The
   same holds for each injected error.
4. **Statuses agree.** Grades from premises equal the statuses recorded in
   `replication/examples.py` and the tutorial outputs, claim by claim.
5. **Templates retire safely.** For each claim kind with a template, a
   generated `example` proves that the new theorem implies the template's
   statement, on every corpus file of that kind. Only then is the template
   deleted.
6. **Golden files.** The generated Lean for a few programs is pinned, so a
   change in translation shows up as a reviewed diff.

## Milestones

Each milestone ends tested on the corpus, documented and pushed.

1. **Coverage table.** This proposal, the constructor table and a test that
   every constructor and operation is classified. No Lean.
2. **Level A library.** `StatClaim/Interface/`, the generator and its `--check`,
   abstract outcome models and null forms.
3. **Single analyses.** Translation of models, designs, nulls, analyses (exact,
   cited, declared) and claims; the corpus Lean build; tests 1 and 2.
4. **Compositions and grades.** The `statclaim` tactic and its rule set;
   Bonferroni, fixed sequence, graphical and alpha-spending families proved by
   it; the dependency collector and grades from premises; test 4.
5. **Exact modules and templates.** Emitters for the exact modules, with their
   numerical certificates and, for association, a bridge from the module's
   theorems to the core objects; template equivalence and retirement; test 5.
6. **Rejection and reports.** Error-injection agreement (test 3); a
   compatibility certificate from `statclaim report`; the studio shows it where
   Lean is available.

## Not in scope

- Level B for methods that are not candidates for a proof.
- Proving cited guarantees.
- Lean meaning for planning searches, simulations and precision targets; they
  stay calculations.

## Open questions

- Should `statclaim check` always produce the compatibility certificate, or
  only on request? It costs a Lean build.
- What is the CI time budget for the corpus build, and does it need its own
  shard?
- How are premises named so names stay stable across versions? Proposed:
  method key, version and assumption id.
- Should a declared test's premise state the guarantee the author claims, or
  only its fit to the design?
- Heavy numerical checks (exact power, search minimality) stay split per
  candidate, as today; a single proof over all candidates has exhausted memory
  before.

## Risks

- **Trusted translator.** Mitigated by a small table, golden files and audit of
  the canonical input.
- **Python and Lean diverge.** Mitigated by tests 2 to 4 on every change.
- **A false premise**, such as a cited guarantee stated more strongly than the
  literature supports, makes its conclusion empty. Only statistical review of
  premise statements guards against this; they become the trust base, smaller
  and more precise than today's.
- **Contradictory premises** would make every claim hold trivially. The
  satisfiability witness in each generated file rules this out mechanically.
- **Build time and memory.** Mitigated by one shared build, contract facts by
  `decide`, and numerical checks split per candidate.
- **Proof search is slow or brittle.** Lemma sets change with Mathlib versions,
  and search can stall. Mitigated by the pinned toolchain, heartbeat budgets per
  claim, corpus tests on every change, and explicit proofs as a fallback.
- **Scope creep.** Mitigated by the table: anything not translated says so, and
  Level B stays selective.
