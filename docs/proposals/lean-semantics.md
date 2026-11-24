# Proposal: the meaning of a program, defined in Lean

Status: approved 2026-11-24. Open questions 1 and 2 are decided as proposed; how
the paper describes this waits until the spike and phase 1 show how it goes.

Progress:

- Milestone 0 done: go. `StatClaim/Semantics/` defines, for two-sided Fisher tests,
  cited trial tests, Bonferroni families, graphical procedures and fixed sequences:
  the program as data (`Syntax`), its instance, premises and claims (`Meaning`), its
  contract checks (`Contracts`) and grades (`Grades`), 469 trusted lines, and proves
  once that every program's premises hold together (`Theorems`).
  `tests/lean/Semantics.lean` states `examples/mixed_endpoints.stat` and
  `replication/copd/design_cited.stat` this way. Lean accepts `Iff.rfl` between each
  semantic claim and today's statement, so today's proofs prove the new claims
  unchanged. Wrong levels, an unsupported null, too few participants, an overstated
  grade and a missing premise are each refused where expected. No new axioms.

  | Program, CPU seconds | Today | Semantics | Peak memory |
  | --- | --- | --- | --- |
  | `import StatClaim` alone | 1.03 | | 2.96 GB |
  | `mixed_endpoints` | 1.83 | 1.82 | 3.02 GB both |
  | COPD plan | 2.05 | 2.70 | 3.03 GB both |

  The COPD plan costs 1.3 times today's build, inside the 2× limit. Contract checks
  and grades by `decide +kernel` cost nothing measurable; the extra time is Lean
  comparing the semantic claim of the sequence with its proof.

- Milestone 1 done. The data follows the canonical program, field for field, for the
  kinds milestone 0 covers: a model carries everything it declares, a design and a null
  each carry their model, and a key the canonical program writes only when declared is
  an `Option` or a list. `Encode.lean` writes the data's canonical form;
  `lean_translation/data.py` writes the data from the canonical program and refuses any
  key it does not know; `data.binding_problem` compares what Lean prints with the
  canonical program's `verify` claims. `scripts/check_lean_semantics.py`, in
  `make lean-check`, covers 22 corpus programs: Lean's contracts hold for each by
  `decide +kernel`, and each one's data encodes to its canonical program. Every other
  program is listed with the reason it is not covered yet. A Lean test shows that the
  check catches a writer that misreads one arm's size. Trusted Lean: 670 lines
  (`Syntax`, `Meaning`, `Contracts`, `Grades`, `Encode`).

What the spike changed in the design:

- **One instance type for every program.** `Instance` gives a law for each model, and
  a rejection event and slack for each test name, so the trivial instance meets every
  program's premises and non-vacuity is one theorem.
- **Data carries its proofs.** Sizes are `FixedSampleDesign`s and levels
  `SignificanceLevel`s, written with `by decide` and `by norm_num`, so positive
  sizes and levels in [0, 1] are checked by typing.
- **Positions name premises.** `p.premises` lists each request's premises in order;
  a claim's `uses` are positions in that list.
- **Contracts belong to the certified statement.** A null form a model has no
  reading for is read as `True`, the strongest claim; the contracts refuse such
  programs, so the audit requires them.
- **Structural recursion only.** Lean silently compiled a mutual definition by
  well-founded recursion, which does not unfold, when its two motives lived in
  different universes. Every mutual definition now says `termination_by structural`.
- **`decide +kernel` for contracts.** Plain `decide` cannot reduce rational
  arithmetic; the kernel can.

What milestone 1 changed:

- **Laws are keyed by the whole model.** The spike keyed them by arm sizes, so two
  models with the same sizes and different declarations, such as clusters, would have
  shared one law: a statement about fewer studies than Python's.
- **A design that stops by a rule depending on the data claims `False`.** It supplies
  no sampling law, so no claim about it can be stated, and none can be certified.
- **Each view reads its own nulls**, so no definition matches on a model's outcome
  inside a dependent type.
- **Key strings come from the registry.** The generator now writes
  `OutcomeKind.constructor` and `NullKey.key`, which the encoding uses.
- **Order.** The rest of phase 1's syntax arrives with its meaning, in milestones 2 and
  3, each with its encoding. The certificate audit starts comparing the encoding when
  the first programs switch, in milestone 2.

## Goal

Today Python decides what each certified claim says: the translator writes every
statement as Lean text. This proposal moves that decision into Lean. A compiled
program becomes Lean data, and Lean functions define its premises, its claims and
its contract facts. Python then writes only the data and the proofs, and Lean
checks both.

Then a bug in Python can make a build fail, but it cannot change what a
certificate claims.

## Where we are

[The translation](lean-translation.md) is finished: `check` and `report --lean`
build one Lean file per program, and its `program` theorem has the form
`ProgramTheorem Premises Claims`. Each file defines its own `Instance`, `Premises`
and `Claims`, written by Python:

| Trusted Python | Lines | Decides |
| --- | --- | --- |
| `lean_translation/denote.py` | 1,413 | instances, definitions, contract facts, premises, claims |
| `lean_translation/exact.py` | 641 | the claims of exact tests |
| `lean_translation/statements.py` | 700 | the theorems behind exact results, intervals and plans |
| `lean_translation/grades.py` and the collector in each file | 73 | grades |

The corpus, the golden files and the agreement tests guard this code. Its
correctness is still reviewed one generated file at a time.

## The design

### The program as data

`StatClaim/Semantics/Syntax.lean` defines the compiled program as Lean data. It
follows the canonical JSON that certificates already store, without source spans.
Sketch, not final code:

```lean
inductive Model where
  | binomial (control treatment : ℕ)
  | continuous (control treatment : ℕ)
  | survival (control treatment : ℕ)

inductive Test where
  | fisher (design : Design) (null : Null) (alpha : ℚ)
  | cited (method : Generated.MethodKey) (design : Design) (null : Null) (alpha : ℚ)
  | declared (design : Design) (null : Null) (alpha : ℚ)
  | bonferroni (members : List Test) (alpha : ℚ)
  | sequence (members : List Test) (alpha : ℚ)

inductive Request where
  | typeI (test : Test)
  | familywise (test : Test)

structure Program where
  requests : List Request
```

As today, values are identified by their content: two identical models are one
model.

### Its meaning

`StatClaim/Semantics/Meaning.lean` defines, once for every program:

```lean
/-- Everything a program leaves open, the same type for every program: a law for
each model, and a rejection event and slack for each test name. -/
structure Instance where
  laws : Model → AbstractModel
  test : String → (model : Model) → TestInterface (model.view laws).Outcome
  slack : String → ℝ
  graph : String → (vs : List View) → (m : ℕ) → ∀ (Θ Ω : Type) [MeasurableSpace Ω],
    JointStudy Θ Ω → Views Θ Ω vs → Fin m → Set Ω

def Program.Contracts (p : Program) : Prop             -- decidable
def Program.premises (p : Program) : List Premise
def Request.Holds (i : Instance) : Request → Prop

/-- Request `r` holds for every instance meeting the premises at positions `uses`. -/
def Program.ClaimFrom (p : Program) (r : ℕ) (uses : List ℕ) : Prop :=
  ∀ i, p.Using i uses → p.claimAt r i
```

The definitions use the objects that translated files already use: the
`LevelPremise`, `familywiseClaim`, `sequenceClaim` and `MemberView` of
`StatClaim/Interface/`, and each module's analysis and Type I theorem. The
semantics adds no new statistical content. It moves the existing statements into
one definition.

A part the semantics cannot interpret (a reference to the wrong kind of value, for
example) denotes a claim that is `False` and a premise that is `True`. Such a
claim can never be certified, and such a premise can never make a claim vacuous.

### A generated file

```lean
def program : StatClaim.Semantics.Program := { requests := [ ... ] }  -- data, from Python

theorem contracts : program.Contracts := by decide +kernel

theorem claim_0 : program.ClaimFrom 0 [0] := by ...   -- untrusted proof, from Python
theorem claim_1 : program.ClaimFrom 1 [] := by ...

theorem grades : [program.grade 0 [0], program.grade 1 []] = [.conditional, .proved] := by
  decide +kernel
```

The audit checks three things beyond what it checks today:

1. Each certified theorem has exactly the type `program.ClaimFrom r uses`, and
   `contracts` has the type `program.Contracts`.
2. `program`, encoded back to JSON by `StatClaim/Semantics/Encode.lean`, equals
   the canonical program the certificate binds. Python's writer is then
   untrusted too.
3. The grades reported are the ones `grades` proves.

### Grades from the statement

Today a meta-program walks each proof to list the premises it uses, and
`grades.py` turns that list into a grade. Here, the list is part of the
statement: `ClaimFrom r uses` can be proved only if the premises in `uses`
suffice. Lean computes the grade from `uses` and the program, by the rule
`grades.py` uses now. Python chooses `uses`. A list that is too short fails to
build. A list that is too long gives a weaker grade, which the status-agreement
test catches. The collector and its trusted meta-code are deleted.

### Proved once, for every program

`StatClaim/Semantics/Theorems.lean` proves, for every program:

- **The premises can hold together** (`Program.satisfiable`, done): the trivial
  instance, whose tests never reject, meets every premise of every program, without
  any contract. This replaces the witness in each file.
- **Grades never overstate**: adding premises to `uses` never gives a stronger
  grade, and a claim whose `uses` includes a cited or declared premise is never
  graded proved.
- **Large-sample claims keep their slack**: a claim that rests on a
  large-sample premise states its bound with that premise's slack.

These are the general guarantees a separately verified contract checker would give.
Contracts are computed from the data and evaluated by the kernel, so no such checker
is needed.

## Scope

**Phase 1: Type I and familywise claims.** This covers what milestones 3 and 4
of the translation covered: two-arm models (binomial as a concrete law;
continuous and survival as abstract laws), observational studies as abstract
models, fixed and unspecified designs, nulls, two-sided Fisher, cited and
declared tests, Bonferroni families, fixed sequences, interim looks, graphical
procedures and their nesting, including the whole COPD plan.

**Phase 2: exact claims.** This covers the Type I claims of the other exact
tests, results, intervals and planning claims, which are today the job of
`exact.py` and `statements.py`. It waits for a common Lean interface for exact
modules, proposed separately. With that interface, one function
states every exact claim. Without it, phase 2 would copy `statements.py` into
Lean case by case.

A program switches to the semantics only when all its claims are in it, so one
certificate never mixes the two ways of stating claims.

**Not in scope.** The parser, the elaborator and `language.normalize` stay
trusted, for building values faithfully. The `.stat` language and its live
diagnostics do not change. Python keeps its contract checks as the fast first
gate. Calculations and simulations stay outside Lean. The web studio is
unchanged.

## Migration without weakening a certificate

`denote.py` and the new semantics are two independent statements of each claim,
one written in Python and one in Lean. Before a claim kind switches, a
generated `example` proves, on every corpus claim of that kind and for every
instance:

```lean
example (i : program.Instance) : (program.requests.get r).Holds program i ↔ <denote.py's statement>
```

The same is proved for the premises. Lean checks these agreements, so the claims
are not just compared by testing. After the switch, what `denote.py` writes is
used only as proof material: proofs can `rw` with the agreement and reuse
today's proofs unchanged. It is untrusted, as the template proofs became.

## Milestones

Each milestone is tested on the corpus, reports the trusted code's size, and is
pushed.

0. **Spike: go or no-go.** Hand-write the semantics for the fragment of
   `examples/mixed_endpoints.stat` (Fisher, a cited t-test, Bonferroni). Prove the
   agreement for that file and for `replication/copd/design_cited.stat`, the
   largest program. Go only if build time and memory stay within twice today's,
   and the audit finds no new axioms. Otherwise stop and report what failed.
1. **Syntax, encoding and binding.** `Syntax.lean` and `Encode.lean` for phase 1;
   `lean_translation/data.py` writes `program`; the audit checks that the
   encoding equals the canonical program. Nothing is stated through the semantics
   yet.
2. **Single tests.** Extend `Meaning.lean` to phase 1's other single tests:
   declared tests, survival models, observational studies and their cited tests,
   and designs without a sampling law. The corpus checker writes the agreement
   examples for every single-test claim; such programs switch.
3. **Combinations.** Interim looks and the remaining nesting rules (Bonferroni
   families, graphs and fixed sequences are in since milestone 0); agreement
   examples; the COPD plan switches.
4. **Grades and theorems.** The grade function and the non-vacuity theorem exist
   since milestone 0. What remains: the certified statement (contracts and every
   claim with its `uses`), the audit's check of its type, grades proved by
   `decide +kernel`, and the collector deleted. The rejection-agreement table
   (test 3) is re-run; a changed outcome, such as an ill-typed null becoming a
   contract failure, is reviewed and recorded.
5. **Phase 2**, after the common module interface: exact Type I, results,
   intervals and plans, by the same steps. `exact.py` and `statements.py` then
   leave the trusted base.

## The trusted base, before and after

| What | Today | After phase 1 | After phase 2 |
| --- | --- | --- | --- |
| What a claim means | 2,754 lines of Python | `Semantics/` in Lean for phase 1; `exact.py` and `statements.py` for exact claims | `Semantics/` in Lean |
| Grades | `grades.py` and a meta-program in every file | a Lean function, in the statement | same |
| Non-vacuity | a witness in every file | one theorem | same |
| Which program is meant | `denote.py` reads the typed objects | the Lean encoding is compared with the certificate's program | same |
| Values from source | parser, elaborator, `normalize` | unchanged | unchanged |
| Lean library definitions, premise generator, certificate checks, result binding | as in the translation proposal | unchanged | unchanged |

Trust moves; it does not disappear. The Lean semantics is trusted, and a wrong
definition there is as bad as a wrong line of `denote.py`. What improves:

- It is one fixed definition, reviewed once, in the language the theorems are
  in, not text that differs from program to program.
- General properties can be proved about it, as listed above.
- During migration, Lean proves that it agrees with an independent Python
  statement of every corpus claim.

## Risks

- **Kernel cost.** Proofs must unfold the semantics on concrete programs.
  Mitigation: structural recursion only; equation lemmas with `simp only`
  rather than unfolding by `rfl`; contracts by `decide`. The spike measures this
  before anything else is built.
- **Representations differ.** Today's statements use vectors `![a, b]`, while
  the semantics walks lists. A `vecOfList` that reduces to `![…]` on a literal
  list keeps the two definitionally equal. The spike checks this too.
- **Two statements during migration.** Both are kept until each claim kind
  switches, and the agreement examples keep them equal. The overlap ends at
  each switch.
- **The encoder.** If two programs encoded to the same JSON, the binding check
  would accept the wrong one. Prove the encoder injective for phase 1's types;
  where a proof is impractical, test the round trip on the corpus and on
  generated programs, and list the encoder as trusted.
- **Scope.** The compiler has 97 kinds of typed object. The semantics covers
  only the fragment above, and `table.py` keeps saying what is not in Lean.

## What it lets us claim

Accurate after phase 1:

- For programs in the fragment, the claims, premises and contract facts are
  defined in Lean, as functions of the program. A certificate proves those
  definitions applied to the certified program, and Lean checks that the
  program is the one the certificate binds.
- For every program, the premises can hold together, and a grade never
  overstates its premises. Both are proved once.

Not accurate, and not to be said:

- That the `.stat` language is dependently typed or has refinement types. The
  language is unchanged. Lean's types describe the program; the program does not
  get them. What is implemented is still assume-guarantee reasoning.
- That the compiler, parser or elaborator is verified.
- That Python's contract checks are verified. Lean decides the contracts of each
  certified program.

## Decisions and open questions

1. **How closely the Lean data follows the canonical JSON.** Decided: it follows
   the JSON, and Lean code translates it into a smaller core where cases repeat,
   so that translation step is Lean code too.
2. **Phase 2 and the common module interface.** Decided: phase 2 waits for the
   interface. Phase 1 is useful by itself, and phase 2 without the interface would
   mostly copy `statements.py`.
3. **How the paper frames this.** Open until the spike and phase 1 are done. The
   wording rules above apply whatever is chosen.
