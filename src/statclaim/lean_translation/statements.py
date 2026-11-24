"""What each exact certificate states. Trusted: see the trusted base in
docs/proposals/lean-translation.md.

Every theorem a certificate template claims is stated here, once. `verify`'s templates
write these statements into their certificates, and the translator (`exact.py`) writes the
same statements into translated programs, so both state the same thing. Proofs are not
here: they are untrusted, and Lean checks them wherever they are written.

A `Scope` says how names are written: in a certificate, which opens `StatClaim` and
`StatClaim.Modules`, or in a translated program, which names them in full. Arguments
that are Lean terms (a level, a design, a group size) are written by the caller: a
certificate passes the names it declares, a program its own definitions or numbers.
This module imports nothing from StatClaim, so templates and the translator can share it.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class Scope:
    root: str  # how names in StatClaim are written
    modules: str  # how names in StatClaim.Modules are written


CERTIFICATE = Scope("", "")
PROGRAM = Scope("StatClaim.", "StatClaim.Modules.")


@dataclass(frozen=True)
class Theorem:
    """A claimed theorem: its name, its binders and its statement, laid out as the
    certificate writes them."""

    name: str
    binders: str  # as written after the name, with its leading space, or ""
    statement: str  # as written after the colon, with its leading space or line break

    def header(self) -> str:
        """The theorem as a certificate writes it, up to its proof."""
        return f"theorem {self.name}{self.binders} :{self.statement}"

    def proposition(self) -> str:
        """The theorem as one proposition, for a translated program's claim."""
        statement = self.statement.strip()
        if not self.binders.strip():
            return statement
        binders = "\n      ".join(line.strip() for line in self.binders.strip().splitlines())
        return f"∀ {binders},\n      {statement}"

    @property
    def part(self) -> str:
        """The part of a claim it states: its name without `checked_`."""
        return self.name.removeprefix("checked_")


def ratio(numerator: int, denominator: int) -> str:
    """A rational in ℝ, as certificates write it."""
    return f"((({numerator} : ℕ) : ℝ) / (({denominator} : ℕ) : ℝ))"


def point(s: Scope, numerator: int, denominator: int) -> str:
    return f"{s.root}ratPoint {numerator} {denominator} (by decide) (by decide)"


# Fisher's tests of two proportions --------------------------------------------------------
def counts(nc: int, nt: int, xc: int, xt: int) -> Theorem:
    return Theorem("checked_counts", "", f" 0 < {nc} ∧ 0 < {nt} ∧ {xc} ≤ {nc} ∧ {xt} ≤ {nt}")


def support(s: Scope, nc: int, nt: int, total: int, low: int, high: int) -> Theorem:
    return Theorem(
        "checked_support",
        " (k : ℕ)",
        f"\n    k ∈ {s.root}hypergeometricSupport {nc} {nt} {total} ↔\n"
        f"      {low} ≤ k ∧ k ≤ {high}",
    )


def p_value(s: Scope, first: int, second: int, total: int, x: int, value: tuple) -> Theorem:
    return Theorem(
        "checked_p_value",
        "",
        f" {s.root}hypergeometricPValue {first} {second} {total} {x} =\n"
        f"    ({value[0]} : ℚ) / {value[1]}",
    )


def table_probability(
    s: Scope, first: int, second: int, total: int, x: int, value: tuple
) -> Theorem:
    return Theorem(
        "checked_table_probability",
        "",
        f" {s.root}hypergeometricMass {first} {second} {total} {x} =\n"
        f"    ({value[0]} : ℚ) / {value[1]}",
    )


def fisher_decision(s: Scope, nc: int, nt: int, xc: int, xt: int, level: tuple, truth: str):
    region = f"{s.root}fisherRejectionRegionAt {nc} {nt} (({level[0]} : ℚ) / {level[1]})"
    return Theorem("checked_decision", "", f"\n    (({xc}, {xt}) ∈ {region}) ↔ {truth}")


def fisher_typeI(s: Scope, nc: int, nt: int, level: tuple) -> Theorem:
    an, ad = level
    return Theorem(
        "checked_typeI",
        " (p : unitInterval)",
        f"\n    ({s.root}fisherNullLaw {nc} {nt} p).real ({s.root}fisherRejectionRegionAt {nc} "
        f"{nt} (( {an} : ℚ) / {ad})) ≤\n      (({an} : ℝ) / {ad})",
    )


def one_sided_p_value(s: Scope, nc: int, nt: int, total: int, x: int, value: tuple) -> Theorem:
    return Theorem(
        "checked_p_value",
        "",
        f" {s.modules}FisherOneSided.lowerPValue {nc} {nt} {total} {x} =\n"
        f"    ({value[0]} : ℚ) / {value[1]}",
    )


def one_sided_decision(
    s: Scope, nc: int, nt: int, total: int, x: int, level: tuple, truth: str
) -> Theorem:
    return Theorem(
        "checked_decision",
        "",
        f"\n    ({s.modules}FisherOneSided.lowerPValue {nc} {nt} {total} {x} ≤ "
        f"({level[0]} : ℚ) / {level[1]}) ↔ {truth}",
    )


def analysis_typeI(analysis: str, bound: str) -> Theorem:
    """A Type I claim on an analysis: `analysis` and `bound` are Lean terms."""
    return Theorem("checked_typeI", "", f"\n    ({analysis}.typeIClaim {bound}).statement")


def analysis_sizes(sizes: str, nc: int, nt: int) -> Theorem:
    return Theorem(
        "checked_sizes",
        "",
        f" {sizes}.nControl = {nc} ∧ {sizes}.nTreatment = {nt} ∧\n"
        f"    0 < {sizes}.nControl ∧ 0 < {sizes}.nTreatment",
    )


def margin_power(s: Scope, analysis: str, rates: str, power: tuple) -> Theorem:
    """`rates` is the planning point's four numbers and their four checks."""
    return Theorem(
        "checked_power",
        "",
        f"\n    ({analysis}.powerClaim\n"
        f"      (fun parameter => parameter = {s.modules}FisherPower.ratePoint {rates})\n"
        f"      {ratio(*power)}).statement",
    )


def margin_decision(s: Scope, nt: int, thresholds: str, x: int, y: int, verdict: str):
    return Theorem(
        "checked_decision",
        "",
        f"\n    {s.modules}DifferenceTest.rejects {nt} {thresholds} {x} {y} = {verdict}",
    )


# One-arm and two-stage designs -----------------------------------------------------------
def one_sample_p_value(s: Scope, n: int, k: int, rate: tuple, value: tuple) -> Theorem:
    return Theorem(
        "checked_p_value",
        "",
        f"\n    (({s.modules}OneSampleBinomial.policy ⟨{n}, {k}⟩).law ({point(s, *rate)})).real\n"
        f"        {{count | {k} ≤ count}} = {ratio(*value)}",
    )


def one_sample_critical(s: Scope, n: int, rate: tuple, level: tuple, critical: int) -> Theorem:
    return Theorem(
        "checked_critical",
        "",
        f"\n    {s.modules}OneSampleBinomial.criticalValue {n} {rate[0]} {rate[1]} {level[0]} "
        f"{level[1]} = {critical}",
    )


def one_sample_decision(critical: int, k: int, rejects: bool) -> Theorem:
    decision = f"{critical} ≤ {k}" if rejects else f"¬ {critical} ≤ {k}"
    return Theorem("checked_decision", "", f" {decision}")


def one_sample_typeI(s: Scope, n: int, critical: int, rate: tuple, level: tuple) -> Theorem:
    return Theorem(
        "checked_typeI",
        "",
        f"\n    (({s.modules}OneSampleBinomial.analysis ⟨{n}, {critical}⟩ ({point(s, *rate)}))"
        f".typeIClaim\n      {ratio(*level)}).statement",
    )


def stage_interim(design: str, first: int, continued: bool) -> Theorem:
    return Theorem(
        "checked_interim",
        "",
        f"\n    {design}.continues {first} = {'true' if continued else 'false'}",
    )


def stage_decision(design: str, first: int, second: int, rejected: bool) -> Theorem:
    return Theorem(
        "checked_decision",
        "",
        f"\n    {design}.rejects {first} {second} = {'true' if rejected else 'false'}",
    )


def stage_typeI(s: Scope, design: str, null_rate: str, bound: tuple) -> Theorem:
    return Theorem(
        "checked_typeI",
        "",
        f"\n    (({s.modules}TwoStageBinomial.analysisAtMost {design} {null_rate}).typeIClaim\n"
        f"      {ratio(*bound)}).statement",
    )


# Intervals -------------------------------------------------------------------------------
def confidence(s: Scope, n: object, tail: str, count: object) -> str:
    return f"{s.modules}BinomialInterval.confidenceSet {n} {tail} {count}"


def binomial_coverage(s: Scope, n: int, tail: str) -> Theorem:
    return Theorem(
        "checked_coverage",
        " (p : unitInterval)",
        f"\n    1 - 2 * {tail} ≤\n      (ProbabilityTheory.binomial {n} p).real\n"
        f"        {{count | p ∈ {confidence(s, n, tail, 'count')}}}",
    )


def binomial_interval(s: Scope, n: int, x: int, tail: str, lower: tuple, upper: tuple):
    return Theorem(
        "checked_interval",
        f" (p : unitInterval)\n    (member : p ∈ {confidence(s, n, tail, x)})",
        f"\n    {point(s, *lower)} ≤ p ∧\n      p ≤ {point(s, *upper)}",
    )


def joint_coverage(
    s: Scope, level: tuple, n: object, m: object, tail: str, names: tuple = ("x", "y")
) -> Theorem:
    x, y = names
    return Theorem(
        "checked_coverage",
        " (pc pt : unitInterval)",
        f"\n    {ratio(*level)} ≤ ({s.root}productBinomial {n} {m} pc pt).real\n"
        f"      ({{{x} | pc ∈ {confidence(s, n, tail, x)}}} ×ˢ\n"
        f"        {{{y} | pt ∈ {confidence(s, m, tail, y)}}})",
    )


def mixture_coverage(s: Scope, level: tuple, n: str, tail: str) -> Theorem:
    """`n` is the sample size, as a Lean term."""
    return Theorem(
        "checked_coverage",
        " (q pc pt : unitInterval)",
        f"\n    {ratio(*level)} ≤\n"
        f"      ({s.modules}Association.mixture {n} q (fun k => {s.root}productBinomial "
        f"({n} - k) k pc pt)).real\n"
        f"        ({s.modules}Association.given {n} (fun k =>\n"
        f"          {{a | pc ∈ {confidence(s, f'({n} - k)', tail, 'a')}}} ×ˢ\n"
        f"            {{b | pt ∈ {confidence(s, 'k', tail, 'b')}}}))",
    )


def two_arms(s: Scope, n: int, m: int, x: int, y: int, tail: str) -> str:
    """The binders of an interval from two arms' confidence sets."""
    return (
        f" (pc pt : unitInterval)\n"
        f"    (control : pc ∈ {confidence(s, n, tail, x)})\n"
        f"    (treatment : pt ∈ {confidence(s, m, tail, y)})"
    )


def difference_bounds(control: tuple, treatment: tuple) -> str:
    """Bounds on a difference of rates from each arm's endpoints, as a statement."""
    cln, cld, cun, cud = control
    tln, tld, tun, tud = treatment
    return (
        f"\n    (({tln} : ℕ) : ℝ) / (({tld} : ℕ) : ℝ) - (({cun} : ℕ) : ℝ) / (({cud} : ℕ) : ℝ) ≤\n"
        "        (pt : ℝ) - (pc : ℝ) ∧\n"
        "      (pt : ℝ) - (pc : ℝ) ≤\n"
        f"        (({tun} : ℕ) : ℝ) / (({tud} : ℕ) : ℝ) - (({cln} : ℕ) : ℝ) / (({cld} : ℕ) : ℝ)"
    )


def difference_interval(
    s: Scope, n: int, m: int, x: int, y: int, tail: str, control: tuple, treatment: tuple
) -> Theorem:
    return Theorem(
        "checked_interval", two_arms(s, n, m, x, y, tail), difference_bounds(control, treatment)
    )


def odds(s: Scope, value: str) -> str:
    return f"{s.modules}Association.odds {value}"


def effect_interval(s: Scope, kind: str, binders: str, control: tuple, treatment: tuple) -> Theorem:
    """An interval for a difference, ratio or odds ratio of two groups' rates."""
    cln, cld, cun, cud = control
    tln, tld, tun, tud = treatment
    if kind == "difference":
        statement = (
            f"{ratio(tln, tld)} - {ratio(cun, cud)} ≤ (pt : ℝ) - (pc : ℝ) ∧\n"
            f"      (pt : ℝ) - (pc : ℝ) ≤ {ratio(tun, tud)} - {ratio(cln, cld)}"
        )
        return Theorem("checked_interval", binders, f"\n    {statement}")
    if kind == "ratio":
        binders += "\n    (positive : 0 < (pc : ℝ))"
        statement = f"{ratio(tln, tld)} / {ratio(cun, cud)} ≤ (pt : ℝ) / pc"
        if cln > 0:
            statement += f" ∧\n      (pt : ℝ) / pc ≤ {ratio(tun, tud)} / {ratio(cln, cld)}"
        return Theorem("checked_interval", binders, f"\n    {statement}")
    binders += (
        "\n    (positive : 0 < (pc : ℝ)) (below : (pc : ℝ) < 1) (treatedBelow : (pt : ℝ) < 1)"
    )
    effect = f"{odds(s, 'pt')} / {odds(s, 'pc')}"
    statement = (
        f"{odds(s, ratio(tln, tld))} / {odds(s, ratio(cun, cud))} ≤ {effect}"
        if cun < cud
        else f"0 ≤ {effect}"
    )
    if cln > 0 and tun < tud:
        statement += f" ∧\n      {effect} ≤ {odds(s, ratio(tun, tud))} / {odds(s, ratio(cln, cld))}"
    return Theorem("checked_interval", binders, f"\n    {statement}")


def odds_interval(s: Scope, n: int, x: int, tail: str, lower: tuple, upper: tuple, scale: str):
    """Bounds on an odds, times a scale, from a share's confidence set. No upper bound when
    the share's upper endpoint is one."""
    statement = f"{odds(s, ratio(*lower))}{scale} ≤ {odds(s, 'π')}{scale}"
    if upper[0] < upper[1]:
        statement += f" ∧\n      {odds(s, 'π')}{scale} ≤ {odds(s, ratio(*upper))}{scale}"
    return Theorem(
        "checked_interval",
        f" (π : unitInterval)\n    (member : π ∈ {confidence(s, n, tail, x)}) "
        "(below : (π : ℝ) < 1)",
        f"\n    {statement}",
    )


# Observational designs -------------------------------------------------------------------
def groups_sizes(first: str, second: str, sizes: tuple) -> Theorem:
    """`first` and `second` are the group sizes as Lean terms; `sizes` their values."""
    return Theorem(
        "checked_sizes",
        "",
        f" {first} = {sizes[0]} ∧ {second} = {sizes[1]} ∧ 0 < {first} ∧\n    0 < {second}",
    )


def groups_typeI(s: Scope, first: str, second: str, level: str, bound: str = "") -> Theorem:
    """`level` is the level's value in ℚ, as a Lean term; the bound is the level unless a
    plan requests another."""
    return Theorem(
        "checked_typeI",
        " (p : unitInterval)",
        f"\n    ({s.root}fisherNullLaw {first} {second} p).real\n"
        f"        ({s.root}fisherRejectionRegionAt {first} {second} {level}) ≤\n"
        f"      {bound or f'({level} : ℝ)'}",
    )


def total_size(n: str, value: int) -> Theorem:
    return Theorem("checked_size", "", f" {n} = {value} ∧ 0 < {n}")


def mixture_law(s: Scope, n: str) -> Theorem:
    return Theorem(
        "checked_law",
        " (q p : unitInterval)",
        f"\n    {s.modules}Association.mixtureLaw {n} q p Set.univ = 1",
    )


def mixture_typeI(s: Scope, n: str, level: str, bound: str = "") -> Theorem:
    return Theorem(
        "checked_typeI",
        " (q p : unitInterval)",
        f"\n    ({s.modules}Association.mixtureLaw {n} q p).real\n"
        f"        ({s.modules}Association.mixtureRejection {n} {level}) ≤\n"
        f"      {bound or f'({level} : ℝ)'}",
    )


def association_decision(s: Scope, table: str, region: str, truth: str) -> Theorem:
    """`table` is the observed table and `region` the rejection region, as Lean terms."""
    return Theorem("checked_decision", "", f" ({table} ∈ {region}) ↔ {truth}")


def rate_typeI(s: Scope, level: str, bound: str = "") -> Theorem:
    """For every total rate and every share of person-time, under equal rates."""
    return Theorem(
        "checked_typeI",
        " (total : NNReal) (share : unitInterval)",
        f"\n    ({s.modules}Incidence.ratesLaw total share).real\n"
        f"        ({s.modules}Incidence.given (fun n => {s.modules}Incidence.rejectionAt share n "
        f"({level} : ℝ))) ≤\n      {bound or f'({level} : ℝ)'}",
    )


def tails(s: Scope, n: int, share: tuple, x: int, upper: int, lower: int) -> Theorem:
    a, d = share
    return Theorem(
        "checked_tails",
        "",
        f" {s.modules}OneSampleBinomial.tailNumerator {n} {a} {d} {x} = {upper} ∧\n"
        f"    {s.modules}BinomialInterval.lowerNumerator {n} {a} {d} {x} = {lower}",
    )


def rate_decision(s: Scope, n: int, x: int, share: str, level: str, truth: str) -> Theorem:
    return Theorem(
        "checked_decision",
        "",
        f"\n    (({n}, {x}) ∈ {s.modules}Incidence.given (fun n => {s.modules}Incidence."
        f"rejectionAt {share} n\n      ({level} : ℝ))) ↔ {truth}",
    )


def rate_coverage(s: Scope, level: tuple, tail: str) -> Theorem:
    return Theorem(
        "checked_coverage",
        " (total : NNReal) (π : unitInterval)",
        f"\n    {ratio(*level)} ≤ ({s.modules}Incidence.ratesLaw total π).real\n"
        f"      ({s.modules}Incidence.given (fun n => {{x | π ∈ "
        f"{confidence(s, 'n', tail, 'x')}}}))",
    )


def pairs_size(pairs: str, value: int) -> Theorem:
    return Theorem("checked_size", "", f" {pairs} = {value} ∧ 0 < {pairs}")


def pairs_law(s: Scope, pairs: str) -> Theorem:
    return Theorem(
        "checked_law",
        " (δ π : unitInterval)",
        f" {s.modules}Matched.pairsLaw {pairs} δ π Set.univ = 1",
    )


def pairs_typeI(s: Scope, pairs: str, level: str, bound: str = "") -> Theorem:
    return Theorem(
        "checked_typeI",
        " (δ : unitInterval)",
        f"\n    ({s.modules}Matched.pairsLaw {pairs} δ {s.modules}Matched.half).real\n"
        f"        ({s.modules}Matched.pairsRejection {pairs} ({level} : ℝ)) ≤ "
        f"{bound or f'({level} : ℝ)'}",
    )


def pairs_decision(s: Scope, d: int, x: int, pairs: str, level: str, truth: str) -> Theorem:
    return Theorem(
        "checked_decision",
        "",
        f"\n    (({d}, {x}) ∈ {s.modules}Matched.pairsRejection {pairs} ({level} : ℝ)) ↔ {truth}",
    )


def pairs_coverage(s: Scope, level: tuple, pairs: str, tail: str) -> Theorem:
    return Theorem(
        "checked_coverage",
        " (δ π : unitInterval)",
        f"\n    {ratio(*level)} ≤ ({s.modules}Matched.pairsLaw {pairs} δ π).real\n"
        f"      ({s.modules}Association.given {pairs}\n"
        f"        (fun d => {{x | π ∈ {confidence(s, 'd', tail, 'x')}}}))",
    )


# Randomisation tests ---------------------------------------------------------------------
def randomisation_typeI(
    s: Scope,
    level: str,
    draws: str = "",
    units: str = "",
    treated: str = "",
    groups: str = "",
) -> Theorem:
    """For every statistic and all outcomes under the sharp null, under the declared
    assignment: complete (`units`, `treated`) or by groups. With `draws`, the p-value is
    estimated from that many independent draws of the assignment."""
    r = f"{s.modules}Randomisation"
    if groups:
        record = "Record"
        statistic = f"{r}.GroupedAssignment {groups} → Record → Statistic"
        outcomes = f"{r}.GroupedAssignment {groups} → Record"
        sharp = "∀ first second, outcomes first = outcomes second"
        law = f"{r}.groupedLaw {groups}"
    else:
        record = "Value"
        statistic = f"{r}.Assignment {units} → (Fin {units} → Value) → Statistic"
        outcomes = f"{r}.PotentialOutcomes {units} Value"
        sharp = f"{r}.SharpNull outcomes"
        law = f"{r}.law {units} {treated}"
    binders = (
        f" {{{record} : Type}} {{Statistic : Type}} [LinearOrder Statistic]\n"
        f"    (statistic : {statistic})\n"
        f"    (outcomes : {outcomes})\n"
        f"    (sharp : {sharp})"
    )
    if draws:
        statement = (
            f"\n    (MeasureTheory.Measure.pi (fun _ : Fin ({draws} + 1) => {law})).real\n"
            f"        ({r}.drawnRejection {draws} statistic outcomes {level}) ≤\n"
            f"      ({level} : ℝ)"
        )
    elif groups:
        statement = (
            f"\n    ({law}).real\n"
            f"        ({r}.uniformRejection ({r}.groupedSplits {groups}) statistic outcomes\n"
            f"          {level}) ≤ ({level} : ℝ)"
        )
    else:
        statement = (
            f"\n    ({law}).real\n"
            f"        ({r}.rejection {units} {treated} statistic outcomes {level}) ≤\n"
            f"      ({level} : ℝ)"
        )
    return Theorem("checked_typeI", binders, statement)


# Plans -----------------------------------------------------------------------------------
# A plan's statements name the definitions its certificate declares. A translated program
# declares the same definitions in a namespace of the claim's own, from these functions.
def level_definition(s: Scope, level: tuple) -> str:
    return (
        f"def declaredLevel : {s.root}SignificanceLevel :=\n"
        f"  ⟨({level[0]} : ℚ) / {level[1]}, by norm_num, by norm_num⟩"
    )


def fisher_plan_definitions(s: Scope, module: str, nc: int, nt: int, level: tuple, rates: str):
    """A design of two arms: `module` is FisherPower (two-sided) or FisherOneSided, and
    `rates` the planning point's four numbers and their four checks."""
    return (
        f"def declaredSizes : {s.root}FixedSampleDesign := ⟨{nc}, {nt}, by decide, by decide⟩\n"
        f"{level_definition(s, level)}\n"
        f"noncomputable def declaredAnalysis := {s.modules}{module}.analysis declaredSizes "
        "declaredLevel\n"
        f"noncomputable def planningPoint : {s.modules}TwoArmBinomial.Parameters :=\n"
        f"  {s.modules}FisherPower.ratePoint {rates}"
    )


def fisher_power(analysis: str, planning: str, power: tuple) -> Theorem:
    return Theorem(
        "checked_power",
        "",
        f"\n    ({analysis}.powerClaim (fun parameter => parameter = {planning})\n"
        f"      {ratio(*power)}).statement",
    )


def fisher_smaller(
    s: Scope, module: str, low: int, n: int, r: int, planning: str, level: str, power: tuple
) -> Theorem:
    """Every smaller design in the search, `r` times as many treated, falls short of power."""
    sizes = f"⟨n, {r} * n, positive, Nat.mul_pos (by decide) positive⟩"
    return Theorem(
        "checked_smaller",
        f" (n : ℕ) (positive : 0 < n) (lower : {low} ≤ n) (upper : n < {n})",
        f"\n    (({s.root}Core.Policy.fixed ({s.modules}TwoArmBinomial.model\n"
        f"        {sizes})).law {planning}).real\n"
        f"        ({s.modules}{module}.analysis {sizes}\n"
        f"          {level}).rejection <\n"
        f"      {ratio(*power)}",
    )


def policy_definitions(s: Scope, module: str, design: str, rate: tuple, analysis: str) -> str:
    """A one-arm or two-stage design: `design` is its term, written by the caller."""
    return (
        f"def declaredDesign : {s.modules}{module}.Design :=\n"
        f"  {design}\n"
        f"noncomputable def nullRate : unitInterval := {point(s, *rate)}\n"
        f"noncomputable def declaredAnalysis := {s.modules}{module}.{analysis} declaredDesign "
        "nullRate"
    )


def policy_stages(shape: str) -> Theorem:
    return Theorem("checked_stages", "", f" {shape}")


def policy_power(s: Scope, analysis: str, alternative: tuple, power: tuple) -> Theorem:
    return Theorem(
        "checked_power",
        "",
        f"\n    ({analysis}.powerClaim (fun rate => rate = {point(s, *alternative)})\n"
        f"      {ratio(*power)}).statement",
    )


def policy_smaller(
    s: Scope,
    low: int,
    n: int,
    rate: tuple,
    level: tuple,
    error: tuple,
    alternative: tuple,
    power: tuple,
) -> Theorem:
    """Every smaller one-arm design in the search exceeds the error bound or falls short of
    power."""
    m = f"{s.modules}OneSampleBinomial"
    design = f"{m}.levelDesign n {rate[0]} {rate[1]} {level[0]} {level[1]}"
    return Theorem(
        "checked_smaller",
        f" (n : ℕ) (lower : {low} ≤ n) (upper : n < {n})",
        f"\n    {ratio(*error)} <\n"
        f"        (({m}.policy ({design})).law\n"
        f"          ({point(s, *rate)})).real\n"
        f"          {{count | ({design}).critical ≤ count}} ∨\n"
        f"      (({m}.policy ({design})).law\n"
        f"          ({point(s, *alternative)})).real\n"
        f"          {{count | ({design}).critical ≤ count}} <\n"
        f"        {ratio(*power)}",
    )


def groups_power(s: Scope, first: str, second: str, rates: str, level: str, power: tuple):
    """`rates` is the two groups' planning probabilities, as Lean terms."""
    return Theorem(
        "checked_power",
        "",
        f"\n    {ratio(*power)} ≤\n"
        f"      ({s.root}productBinomial {first} {second} {rates}).real\n"
        f"        ({s.root}fisherRejectionRegionAt {first} {second} {level})",
    )


def groups_smaller(s: Scope, low: int, n: int, r: int, rates: str, level: str, power: tuple):
    return Theorem(
        "checked_smaller",
        f" (n : ℕ) (lower : {low} ≤ n) (upper : n < {n})",
        f"\n    ({s.root}productBinomial ({r} * n) n {rates}).real\n"
        f"        ({s.root}fisherRejectionRegionAt ({r} * n) n {level}) <\n"
        f"      {ratio(*power)}",
    )


def pairs_power(s: Scope, pairs: int, rates: str, level: str, power: tuple) -> Theorem:
    return Theorem(
        "checked_power",
        "",
        f"\n    {ratio(*power)} ≤ ({s.modules}Matched.pairsLaw {pairs} {rates}).real\n"
        f"        ({s.modules}Matched.pairsRejection {pairs} ({level} : ℝ))",
    )


def pairs_smaller(s: Scope, low: int, n: int, rates: str, level: str, power: tuple) -> Theorem:
    return Theorem(
        "checked_smaller",
        f" (m : ℕ) (lower : {low} ≤ m) (upper : m < {n})",
        f"\n    ({s.modules}Matched.pairsLaw m {rates}).real\n"
        f"        ({s.modules}Matched.pairsRejection m ({level} : ℝ)) < {ratio(*power)}",
    )


def events_power(s: Scope, n: int, alternative: str, null: str, level: str, power: tuple):
    return Theorem(
        "checked_power",
        "",
        f"\n    {ratio(*power)} ≤ (ProbabilityTheory.binomial {n} {alternative}).real\n"
        f"        ({s.modules}Incidence.rejectionAt {null} {n} ({level} : ℝ))",
    )


def events_smaller(
    s: Scope, low: int, n: int, alternative: str, null: str, level: str, power: tuple
) -> Theorem:
    return Theorem(
        "checked_smaller",
        f" (m : ℕ) (lower : {low} ≤ m) (upper : m < {n})",
        f"\n    (ProbabilityTheory.binomial m {alternative}).real\n"
        f"        ({s.modules}Incidence.rejectionAt {null} m ({level} : ℝ)) <\n"
        f"      {ratio(*power)}",
    )


def total_power(s: Scope, n: int, share: str, rates: str, level: str, power: tuple) -> Theorem:
    return Theorem(
        "checked_power",
        "",
        f"\n    {ratio(*power)} ≤\n"
        f"      ({s.modules}Association.mixture {n} {share}\n"
        f"        (fun k => {s.root}productBinomial ({n} - k) k {rates})).real\n"
        f"        ({s.modules}Association.mixtureRejection {n} {level})",
    )
