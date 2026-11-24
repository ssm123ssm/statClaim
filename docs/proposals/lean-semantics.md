# Proposal: the meaning of a program, defined in Lean

Status: approved 2026-11-24. Open questions 1 and 2 are decided as proposed; how
the paper describes this waits until the spike and phase 1 show how it goes.

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
/-- The abstract parts: a law for each continuous or survival model, and a
rejection event and slack for each cited or declared test. -/
structure Program.Instance (p : Program) : Type 1 where
  model : Fin p.abstractModels.length → AbstractModel
  test : (k : Fin p.assumedTests.length) → TestInterface (model (p.modelOf k)).Outcome
  slack : Fin p.assumedTests.length → ℝ

def Program.Contracts (p : Program) : Prop            -- decidable
def Program.premise (p : Program) (k : Fin p.premiseCount) : p.Instance → Prop
def Request.Holds (p : Program) (i : p.Instance) : Request → Prop

/-- Request `r` follows from the premises listed in `uses`, and from no others. -/
def Program.ClaimFrom (p : Program) (r : Fin p.requests.length) (uses : List (Fin p.premiseCount)) : Prop :=
  ∀ i, (∀ k ∈ uses, p.premise k i) → (p.requests.get r).Holds p i
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

theorem contracts : program.Contracts := by decide

theorem claim_0 : program.ClaimFrom 0 [0] := by ...   -- untrusted proof, from Python
theorem claim_1 : program.ClaimFrom 1 [] := by ...

theorem grades : program.grades [[0], []] = [.conditional, .proved] := by decide
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

- **The premises can hold together**: `p.Contracts → ∃ i, ∀ k, p.premise k i`,
  witnessed by tests that never reject. This replaces the witness in each file.
- **Grades never overstate**: adding premises to `uses` never gives a stronger
  grade, and a claim whose `uses` includes a cited or declared premise is never
  graded proved.
- **Large-sample claims keep their slack**: a claim that rests on a
  large-sample premise states its bound with that premise's slack.

These are the general results suggestion 2 asked for. Contracts become decidable
propositions that the kernel evaluates, so a separate verified checker is not
needed.

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
modules (suggestion 4, proposed separately). With that interface, one function
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
2. **Single tests.** `Meaning.lean` for models, designs, nulls and tests;
   agreement examples for every single-test claim in the corpus; such programs
   switch.
3. **Combinations.** Families, sequences, looks, graphs and nesting; agreement
   examples; the COPD plan switches.
4. **Grades and theorems.** `ClaimFrom` with `uses`, grades proved by `decide`,
   the collector deleted, `Theorems.lean`. The rejection-agreement table (test 3)
   is re-run; a changed outcome, such as an ill-typed null becoming a contract
   failure, is reviewed and recorded.
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
