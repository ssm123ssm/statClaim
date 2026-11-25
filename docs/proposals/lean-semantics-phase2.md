# Proposal: exact claims in the semantics, and retiring the translator

Status: implemented. This completes phase 2 of
[the semantics proposal](lean-semantics.md).

## Implementation

`Program.sound` now issues every whole-program certificate. The covered claims
include exact Type I and familywise bounds, observed results, confidence intervals,
and exact planning. Lean checks the contracts and numerical hints. The certificate
binds the canonical program and the reported values it proves. Blinded sample-size
re-estimation and simulated Type I remain outside Lean. Programs without claims can
still have their declarations checked.

The corpus check covers 111 compiled programs and 138 proved claims. It includes
138 frozen translator claims from 80 pinned programs. Six proofs of agreement use
arithmetic normalization where equivalent numerical expressions have different Lean
forms. The independent reference file covers all request and test constructors.
The rejection table asks Lean about 38 programs Python rejects or leaves unresolved.

The semantics directory contains 3,992 lines, including its definitions, encoding
and proofs. The translator and its statement templates have been removed. Version
3 certificates replay through the semantics. Earlier bundles replay with the
StatClaim version that issued them.

## Spike result

Milestone 0 passes for `examples/one_sided.stat`. Lean proves Type I, the
observed result, and the minimum sample size through `Program.sound`. Each
statement agrees definitionally with the live translator. The checker also
audits dependencies and checks that Lean rejects a wrong null, missing hints,
a wrong p-value, and a wrong decision. Run it with `make lean-check`.

Across three runs per path with the library already built, median Lean check
time was 7.92 s for the translator and 7.80 s for the semantics. Median peak
resident memory was 4.28 GiB and 4.43 GiB, respectively. Both are within the
2× limit. The Lean files containing trusted semantic definitions grew from
928 to 1,289 lines, including the adapter's kernel-checked proofs.

The spike now checks the frozen translator statements and exercises kernel and
report binding failures.

## Goal

Finish moving what certificates claim into Lean. Every claim a certificate states
becomes a Lean function of the program, and Python writes only data and hints. Then
the translator is deleted, and its job as an independent second statement of each
claim passes to fixed tests.

## Baseline before phase 2

The compiler accepts 111 corpus programs. At the baseline, 60 had certificates through
the semantics and 51 used the translator, for 82 claims:

| Claims | Count | What they need |
| --- | --- | --- |
| Type I of exact tests: randomisation 9, Fisher's exact test of association 6, one-sided and margin Fisher 2, McNemar 1, rate 1 | 19 | an exact module's level |
| Type I of tests phase 1 covers, in programs with another uncovered part | 4 | the rest of their program |
| Familywise, with an exact member | 5 | their members |
| Results for observed data | 17 | p-values and decisions |
| Intervals | 15 | coverage and endpoints |
| Sample sizes | 11 | power, and failure at smaller sizes |
| A design meets a planning target | 11 | power at a planning point |

Of the 51 programs, two declare sample-size re-estimation, which the translator
records as outside Lean, and two state no claim.

Python defined these claims in the following modules:

| Trusted Python | Lines | Decides |
| --- | --- | --- |
| `lean_translation/denote.py` | 1,446 | definitions, contract facts, premises, claims |
| `lean_translation/exact.py` | 641 | the claims of exact tests, results, intervals and plans |
| `lean_translation/statements.py` | 700 | about 50 theorem statements, one or more per module |
| `lean_translation/grades.py` and the collector | 73 | grades |

## The common interface for exact modules

Every exact module already proves its guarantees one way: a statement, a check the
kernel decides using hints Python computes, and a lemma that a passing check proves
the statement (`FisherOneSided.typeI_of_hints`, `OneSampleBinomial.typeI_of_check`,
`FisherPower.power_of_check`, ...). `statements.py` writes each of these statements
again in Python, one function per theorem. The interface makes the pattern one Lean
structure, so the semantics can state every exact claim with one function:

```lean
/-- One kind of claim an exact module supports. -/
structure Checked (Input : Type) where
  Statement : Input → Prop
  Hint : Type
  check : Input → Hint → Bool
  sound : ∀ x h, check x h = true → Statement x

/-- What an exact module offers the semantics. -/
structure ExactModule where
  Input : Type                -- sizes, counts, rates and levels, as data
  view : Input → View         -- its concrete law, as a model's view in phase 1
  typeI : Checked Input       -- seen from outside: a rejection event and its bound
  result : Option (Checked (Input × Observed × Reported))
  interval : Option (Checked (Input × Observed × Endpoints))
  power : Option (Checked (Input × Point × Target))
```

Four rules:

- **Statements are written once, in Lean.** A module's `Statement`s are the claims
  `statements.py` writes today; the agreement check shows they are the same.
- **Type I is a test seen from outside**, with a rejection event and a bound under
  the module's law, so an exact test enters families the way Fisher's test does in
  phase 1 (`Test.outside`, `fisher_bound`).
- **Hints are not part of the claim.** They are plain lists of numbers, written by
  Python and checked by `decide +kernel`. A wrong hint fails the build; it cannot
  change what is claimed.
- **Grades are unchanged.** An exact claim is proved unless it rests on a premise.

The semantics gains `Test.exact name module design null alpha` and three claim kinds:
`result`, `interval` and `plan` (sample size and meets). The soundness theorem takes
the program's hints:

```lean
theorem Program.sound (p : Program) (contracts : p.Contracts) (r : ℕ)
    (ready : p.readyAt r = true) (hints : p.Hints r)
    (checked : p.checkAt r hints = true) : p.Claim r
```

It is still proved once. For each program, the kernel runs the same checks it
runs today.

## Retiring the translator

The live translator checks each kind as it moves, as in phase 1. Once every kind has
moved:

1. **Freeze the agreement checks.** Generate them one last time and commit them as
   Lean tests: each states one corpus claim as the translator wrote it, and Lean
   accepts that it is the semantic claim. Only the translator's statements are
   frozen. The data is still written by `data.py` from pinned copies of the corpus
   programs, so a later change to the data's syntax does not break the fixtures.
2. **Write one reference statement per claim kind.** A short, reviewed Lean file
   states one example of each kind directly in its module's terms, and Lean checks
   it against the semantics. A test requires every claim kind and test constructor
   to appear there, so a kind added later brings its own independent statement.
3. **Delete the translation.** `denote.py`, `exact.py`, `statements.py`, `prove.py`,
   `program.py`, `grades.py` and the collector go; so do the translation branch of
   `certificate.py`, `scripts/check_lean_translation.py` and the translation column
   of the rejection table. `table.py` stays, pointing at `StatClaim/Semantics/`.
4. **Move what reads it.** `verification.py`, `program_evidence.py`, `lean_report.py`,
   the contract reports and the studio's Lean check read the semantic certificate.
   The proof material in the modules (`planning.py`, `association.py`, ...) writes
   hints only. Certificates issued earlier replay with the version that issued
   them, as when the templates were retired.

What stays as checks: the frozen agreement tests, the reference statements, the
binding check, the grade check, the rejection table on the semantics, and the
soundness proof.

## Milestones

All done (946c810). Each milestone was tested on the corpus, checked agreement with
the live translator, re-ran the rejection table and reported the trusted Lean's size.

0. **Spike: go or no-go.** The interface, with one-sided Fisher ported: Type I with
   hints, its result and its power plan (`examples/one_sided.stat`). Go if the build
   stays within twice today's time and memory, the soundness theorem is still proved
   once, and no axioms are added.
1. **Type I of every exact test**, and families with exact members: randomisation,
   association, McNemar, rate, one-sided and margin Fisher, one-sample and two-stage
   binomial (24 claims).
2. **Results** (17 claims).
3. **Intervals** (15 claims).
4. **Plans**: sample sizes and planning targets (22 claims).
5. **Loose ends.** Re-estimation recorded as outside Lean, as the translator records
   it; programs with no claim; Type I judged by simulation stays outside Lean.
6. **Freeze**: the agreement fixtures and the reference statements.
7. **Retire the translator**, as above.

## The trusted base, before and after

| What | Today | After |
| --- | --- | --- |
| What an exact claim means | `denote.py`, `exact.py`, `statements.py`: 2,787 lines of Python | the interface and each module's statements, in Lean |
| Grades | `grades.py` and a collector for 51 programs | `Program.grade` for every program |
| Which program is meant | the binding check for 60 programs | the binding check for every program |
| Values from source | parser, elaborator, `normalize` | unchanged |

Trusted Lean grows by the interface and the module statements. Most of those
statements are trusted today already, as library definitions; each milestone
reports the new size.

## Risks

- **Kernel cost.** Checking hints through a general interface may unfold more than
  today's direct lemmas. The spike measures this first.
- **Results bind to a run.** A result's p-value comes from a run, not from the
  canonical program. The data must carry the values the run reports, and the audit
  must compare them, or the certificate would prove a number nobody reported.
- **Fixtures go stale.** If a pinned corpus program changes, its frozen statement no
  longer matches. Such a change must update the pin and the statement together, and
  be reviewed.
- **No second statement for new kinds.** After the translator is gone, only the
  reference statements guard a new claim kind. The rule in step 2 enforces one.

## What it lets us claim

After phase 2: every claim a certificate states is defined in Lean as a function of
the program, Lean checks that the program is the one the certificate binds, and
Python supplies only data and hints.

Not to be said, as before: that the `.stat` language is dependently typed or has
refinement types; that the compiler, parser or elaborator is verified; that Python's
contract checks are verified.

## Decisions

All five were decided as proposed and are implemented.

1. **Hints are an argument of `Program.sound`**, since they do not change what is
   claimed.
2. **Reported values are part of the claim.** A result's p-value and decision, an
   interval's endpoints and a plan's selected size are in the certificate's inputs,
   so a wrong computation fails the proof; `program_evidence.bind_report` compares
   them with the run's report.
3. **Frozen fixtures.** The translator's statements are frozen, and the data is
   written from pinned programs.
4. **The spike's module** was one-sided Fisher: Type I with hints, a result and a
   power plan.
5. **Outside Lean:** sample-size re-estimation and Type I judged by simulation, each
   with its reason in `table.py`.
