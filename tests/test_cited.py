"""Contract-tier analyses: checked against their contract, cited, never verified."""

import json
import subprocess
from pathlib import Path

import pytest

from statclaim.cli import main
from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source, render_report
from statclaim.language_syntax import Source
from statclaim.language_values import Evidence, VerificationResult
from statclaim.methods import ASSUMPTIONS, METHODS
from statclaim.methods.core import SCOPES
from statclaim.verification import digest

ROOT = Path(__file__).resolve().parents[1]
HEAD = (
    "use models.two_arm_continuous\nuse sampling\nuse tests.t\n"
    "let study = two_arm_continuous(n_control=60, n_treatment=60)\n"
)
FIXED = HEAD + "let plan = fixed(model=study)\n"
EQUAL = FIXED + "let null = equal_means(model=study)\n"


def run(text, tmp_path):
    return check_source(Source(text, "cited.stat"), project=ROOT, output=tmp_path / "run")


def codes(text):
    return [d.code for d in compile_source(Source(text)).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def test_every_method_states_scope_assumptions_and_references():
    for method in METHODS.values():
        assert method.scope in SCOPES
        assert method.assumptions and method.references
        assert all(ASSUMPTIONS[item.id] is item for item in method.assumptions)
    assert METHODS["t_test"].scope == "finite_sample"
    assert METHODS["welch_test"].scope == "asymptotic"


def test_changing_a_method_requires_a_new_version():
    """Evidence records the method version, so a silent change would mislead."""
    recorded = json.loads((ROOT / "tests/fixtures/method_versions.json").read_text())
    current = {
        key: {"version": method.version, "sha256": digest(repr(method).encode())}
        for key, method in METHODS.items()
    }
    assert current == recorded, (
        "A cited method changed. Bump its version, then run "
        "'uv run python scripts/update_method_versions.py'."
    )


def test_cited_claim_gives_cited_evidence_without_lean_or_certificate(tmp_path):
    text = (
        EQUAL
        + "let analysis = t_test(design=plan, null=null, alpha=1/20)\n"
        + "let checked = verify(typeI(analysis))\n"
        + "let file = checked.evidence.certificate.file\n"
        + "let scope = checked.claim.scope\n"
    )
    report = run(text, tmp_path)
    value = report["values"]["checked"]
    assert report["status"] == value["status"] == "cited"
    assert not report["backend_invoked"] and not report["certificate_issued"]
    evidence = value["evidence"]
    assert evidence["grade"] == "cited" and evidence["certificate"] is None
    assert evidence["scope"] == report["values"]["scope"] == "finite_sample"
    assert evidence["guarantee"] == {
        "quantity": "type_I_error",
        "relation": "equals",
        "bound": "1/20",
        "null": "mean_treatment = mean_control",
        "scope": "finite_sample",
    }
    assert evidence["sources"] == ["literature"] and evidence["machine_checked"] == "contract"
    assert evidence["method"] == {
        "key": "t_test",
        "version": 1,
        "title": "Two-sided pooled-variance t-test",
    }
    assert {"id": "normal_outcomes", "kind": "distribution"}.items() <= evidence["assumptions"][
        3
    ].items()
    assert evidence["references"] == list(METHODS["t_test"].references)
    assert all(text.startswith("Cited, not checked") for text in evidence["established_properties"])
    assert report["values"]["file"] is None
    rendered = render_report(report, Source(text))
    assert "verified" not in rendered
    assert "cited from the literature; not machine-checked" in rendered


def test_approximate_guarantee_is_worded_and_scoped_differently(tmp_path):
    text = (
        FIXED
        + "let margin = mean_difference_at_most(model=study, value=-2)\n"
        + "let welch = welch_test_one_sided(design=plan, null=margin, alpha=1/40)\n"
        + "let checked = verify(typeI(welch))\n"
    )
    evidence = run(text, tmp_path)["values"]["checked"]["evidence"]
    assert evidence["scope"] == "asymptotic"
    assert (
        "No bound is claimed at the declared sample sizes" in evidence["established_properties"][0]
    )


def test_cited_evidence_can_never_back_a_verified_result():
    claim = (
        compile_source(Source(EQUAL + "verify typeI(t_test(design=plan, null=null, alpha=1/20))\n"))
        .program.requests[0]
        .claim
    )
    cited = Evidence(claim, None, (), ("assumed",), "cited", ("reference",))
    assert VerificationResult(1, claim, "snapshot", "cited", cited).evidence is cited
    with pytest.raises(ValueError, match="checked by Lean"):
        VerificationResult(1, claim, "snapshot", "verified", cited)
    with pytest.raises(ValueError, match="carries a certificate"):
        Evidence(claim, None, (), (), "proved")
    with pytest.raises(ValueError, match="carries a certificate"):
        Evidence(claim, {"certificate_id": "x"}, (), (), "cited")


@pytest.mark.parametrize(
    "tail,code",
    [
        # A one-sided question put to the two-sided test, and the reverse.
        (
            "let null = mean_difference_at_most(model=study, value=0)\n"
            "let a = t_test(design=plan, null=null, alpha=1/20)\n",
            "hypothesis_mismatch",
        ),
        (
            "let null = equal_means(model=study)\n"
            "let a = welch_test_one_sided(design=plan, null=null, alpha=1/20)\n",
            "hypothesis_mismatch",
        ),
        # A null declared for a different study.
        (
            "let other = two_arm_continuous(n_control=10, n_treatment=10)\n"
            "let null = equal_means(model=other)\n"
            "let a = t_test(design=plan, null=null, alpha=1/20)\n",
            "model_mismatch",
        ),
        ("let null = equal_means(model=study)\nlet a = t_test(plan, null, alpha=0)\n", "domain"),
    ],
)
def test_contract_violations_are_reported_while_editing(tail, code):
    assert codes(FIXED + tail) == [code]


def test_binary_and_continuous_methods_do_not_mix():
    text = (
        "use models.two_arm_binomial\nuse tests.fisher\n"
        + EQUAL
        + "let binary = two_arm_binomial(n_control=60, n_treatment=60)\n"
        + "let a = fisher(design=plan, null=equal_proportions(model=binary), alpha=1/20)\n"
    )
    assert codes(text) == ["model_mismatch"]
    assert codes(
        EQUAL.replace("60, n_treatment=60", "1, n_treatment=1") + "let a = "
        "welch_test(design=plan, null=null, alpha=1/20)\n"
    ) == ["domain"]


def test_data_dependent_stopping_leaves_the_cited_claim_unresolved(tmp_path):
    text = (
        HEAD
        + "let plan = adaptive(model=study)\nlet null = equal_means(model=study)\n"
        + "let checked = verify(typeI(t_test(design=plan, null=null, alpha=1/20)))\n"
    )
    assert codes(text) == ["sampling_scope"]
    value = check_source(Source(text, "cited.stat"), project=ROOT)["values"]["checked"]
    assert value["status"] == "unresolved_obligation" and value["evidence"] is None


def test_example_runs_from_the_cli_without_lean(capsys):
    assert main(["check", str(ROOT / "examples/t_test.stat"), "--project", str(ROOT)]) == 0
    assert "Program status: cited" in capsys.readouterr().out


def cited_derivation(text=None):
    text = text or EQUAL + "let analysis = t_test(design=plan, null=null, alpha=1/20)\n"
    compilation = compile_source(Source(text))
    return next(d for d in compilation.derivations if d.name == "analysis").to_dict()


def test_cited_contract_derivation_carries_a_checked_conditional_guarantee():
    record = cited_derivation()
    assert check_derivation(record) == []
    assert record["scope"] == "conditional_guarantee"
    guarantee = record["guarantee"]
    assert guarantee["grade"] == "cited" and guarantee["bound"] == "1/20"
    assert guarantee["given"] == [item.id for item in METHODS["t_test"].assumptions]
    assert "not proved" in record["not_established"]


def test_open_obligation_withholds_the_guarantee():
    record = cited_derivation(
        HEAD
        + "let plan = adaptive(model=study)\nlet null = equal_means(model=study)\n"
        + "let analysis = t_test(design=plan, null=null, alpha=1/20)\n"
    )
    assert check_derivation(record) == []
    assert record["guarantee"] is None and record["scope"] == "compatibility"
    assert [item["code"] for item in record["obligations"]] == ["sampling_scope"]


@pytest.mark.parametrize(
    "change",
    [
        lambda d: d["guarantee"].update(bound="1/100"),
        lambda d: d["guarantee"].update(grade="proved"),
        lambda d: d["guarantee"].update(scope="finite_sample", relation="at_most"),
        lambda d: d["guarantee"]["method"].update(version=2),
        lambda d: d["guarantee"]["given"].pop(),
        lambda d: d.update(guarantee=None),
        lambda d: d.update(scope="compatibility"),
        lambda d: d["subject"].update(test="welch_test"),
        lambda d: d["subject"]["design"].update(stopping="data_dependent"),
        lambda d: d["subject"]["design"]["model"].update(n_control=1, n_treatment=1),
        lambda d: d["steps"][2].update(rule_version=2),
    ],
)
def test_checker_rejects_an_altered_cited_guarantee(change):
    record = cited_derivation()
    change(record)
    assert check_derivation(record)


def test_fisher_derivation_cannot_borrow_a_guarantee():
    text = (ROOT / "tests/fixtures/fisher.stat").read_text()
    record = next(
        d for d in compile_source(Source(text)).derivations if d.name == "analysis"
    ).to_dict()
    assert check_derivation(record) == [] and record["guarantee"] is None
    record["guarantee"] = cited_derivation()["guarantee"]
    assert check_derivation(record)


def test_explanation_shows_the_guarantee_and_its_source(capsys):
    path = str(ROOT / "examples/tutorial/12_continuous_outcome.stat")
    assert main(["explain", path]) == 0
    text = capsys.readouterr().out
    assert "Guarantee, given the assumptions" in text and "not proved in Lean" in text
    assert "Independent check of this derivation: passed." in text


MIXED = (ROOT / "examples/mixed_endpoints.stat").read_text()
TWO_MEANS = (
    EQUAL
    + "let first = t_test(design=plan, null=null, alpha=1/40)\n"
    + "let second = welch_test(design=plan, null=null, alpha=1/40)\n"
    + "use multiplicity.bonferroni\n"
)


def family_derivation(text, name="endpoints"):
    compilation = compile_source(Source(text))
    assert not [d for d in compilation.diagnostics if d.severity == "error"]
    return next(d for d in compilation.derivations if d.name == name).to_dict()


def test_a_family_with_a_cited_member_is_a_conditional_composition():
    record = family_derivation(MIXED)
    assert check_derivation(record) == []
    guarantee = record["guarantee"]
    assert guarantee["grade"] == "conditional" and guarantee["quantity"] == "familywise_error"
    assert guarantee["bound"] == "1/20" and guarantee["scope"] == "finite_sample"
    assert [m["grade"] for m in guarantee["members"]] == ["proved", "cited"]
    assert guarantee["given"] == [
        "prespecified_family",
        "member_guarantee:response",
        "member_guarantee:symptoms",
    ]
    assert "members' own error bounds" in record["not_established"]


def test_a_family_is_only_as_exact_as_its_least_exact_member():
    text = TWO_MEANS + "let endpoints = bonferroni(analyses=[first, second], alpha=1/20)\n"
    record = family_derivation(text)
    assert check_derivation(record) == []
    assert record["guarantee"]["scope"] == "asymptotic"
    assert "No bound is claimed at the declared sample sizes" in record["guarantee"]["sentence"]
    claim = compile_source(Source(text + "verify familywise(endpoints)\n")).program.requests[0]
    assert claim.claim.scope == "asymptotic"


def test_overallocated_or_adaptive_members_withhold_the_family_guarantee():
    over = family_derivation(
        TWO_MEANS + "let endpoints = bonferroni(analyses=[first, second], alpha=1/25)\n"
    )
    assert check_derivation(over) == [] and over["guarantee"] is None
    assert [item["code"] for item in over["obligations"]] == ["allocation"]
    text = (TWO_MEANS + "let endpoints = bonferroni([first, second], alpha=1/20)\n").replace(
        "fixed(model=study)", "adaptive(model=study)"
    )
    adaptive = family_derivation(text)
    assert check_derivation(adaptive) == [] and adaptive["guarantee"] is None
    assert codes(text + "verify familywise(endpoints)\n") == ["sampling_scope"]


@pytest.mark.parametrize(
    "change",
    [
        lambda d: d["guarantee"].update(grade="proved"),
        lambda d: d["guarantee"].update(bound="1/10"),
        lambda d: d["guarantee"]["members"][1].update(grade="proved"),
        lambda d: d["guarantee"]["members"][1].update(level="1/100"),
        lambda d: d["guarantee"]["given"].pop(),
        lambda d: d["subject"].update(alpha="1/100"),
        lambda d: d["subject"]["analyses"][1]["analysis"].update(alpha="1/2"),
        lambda d: d["subject"]["analyses"].pop(),
        lambda d: d["assumptions"].pop(1),
        lambda d: d["steps"].pop(8),
        lambda d: d.update(not_established=""),
    ],
)
def test_checker_rejects_an_altered_family_guarantee(change):
    record = family_derivation(MIXED)
    change(record)
    assert check_derivation(record)


def test_family_argument_rules_stay_simple_and_explained():
    head = TWO_MEANS + "let endpoints = bonferroni(analyses=[first, second], alpha=1/20"
    assert codes(head + ")\n") == []
    # No joint law exists to declare for cited members.
    assert codes(head + ', joint_law="binomial_marginals")\n') == ["sampling_contract"]
    assert codes(TWO_MEANS + "let endpoints = bonferroni(analyses=[first, first], alpha=1/20)\n")
    # A Fisher-only family may now leave joint_law out and stays fully proved.
    fisher = (ROOT / "examples/three_outcomes.stat").read_text()
    short = fisher.replace('    joint_law="binomial_marginals",\n', "")
    assert short != fisher
    compilation = compile_source(Source(short))
    assert compilation.status == "elaborated"
    assert compilation.program.requests[0].claim.subject.joint_law == "binomial_marginals"


def test_statuses_never_overstate_their_evidence():
    claim = compile_source(Source(MIXED)).program.requests[0].claim
    conditional = Evidence(claim, {"certificate_id": "x"}, (), (), "conditional")
    assert conditional.machine_checked == "composition"
    assert conditional.sources == ("lean_proof", "member_guarantees")
    VerificationResult(1, claim, "snapshot", "conditional", conditional)
    with pytest.raises(ValueError, match="checked by Lean"):
        VerificationResult(1, claim, "snapshot", "verified", conditional)


def test_a_lean_claim_without_a_checkout_explains_what_still_works(tmp_path):
    text = (ROOT / "tests/fixtures/fisher.stat").read_text()
    report = check_source(Source(text, "fisher.stat"), project=tmp_path, output=tmp_path / "run")
    assert report["status"] == "unresolved_obligation" and not report["backend_invoked"]
    assert "Cited claims, compile, explain and report need no Lean" in json.dumps(report)


def test_cited_claims_run_outside_a_checkout(tmp_path):
    text = (ROOT / "examples/t_test.stat").read_text()
    report = check_source(Source(text, "t.stat"), project=tmp_path, output=tmp_path / "run")
    assert report["status"] == "cited"


SURVIVAL = (
    "use models.two_arm_survival\nuse sampling\nuse tests.survival\n"
    "let study = two_arm_survival(n_control=200, n_treatment=200)\n"
    "let plan = fixed(model=study)\nlet null = equal_survival(model=study)\n"
)


def test_a_new_outcome_and_its_test_are_registry_entries_only(tmp_path):
    text = SURVIVAL + "let analysis = log_rank(design=plan, null=null, alpha=1/20)\n"
    assert check_derivation(cited_derivation(text)) == []
    report = run(text + "let checked = verify(typeI(analysis))\n", tmp_path)
    evidence = report["values"]["checked"]["evidence"]
    assert report["status"] == "cited" and evidence["scope"] == "asymptotic"
    assert evidence["guarantee"]["limit"] == "the number of events grows"
    assert "independent_censoring" in [item["id"] for item in evidence["assumptions"]]
    # Proportional hazards is a power assumption, not an error-rate one.
    assert not any("proportional" in item["text"].lower() for item in evidence["assumptions"])


def test_outcomes_do_not_mix():
    both = SURVIVAL + "use models.two_arm_continuous\nuse tests.t\n"
    # A null for one outcome cannot be stated about another outcome's model.
    assert codes(both + "let wrong = equal_means(model=study)\n") == ["type"]
    # A test for one outcome cannot be run on another outcome's design.
    assert codes(
        both
        + "let scores = two_arm_continuous(n_control=200, n_treatment=200)\n"
        + "let a = t_test(design=plan, null=equal_means(model=scores), alpha=1/20)\n"
    ) == ["model_mismatch"]
    assert codes(
        both
        + "let scores = two_arm_continuous(n_control=200, n_treatment=200)\n"
        + "let a = log_rank(design=fixed(model=scores), null=null, alpha=1/20)\n"
    ) == ["model_mismatch"]


def test_contract_guidance_lists_the_tests_for_the_outcome():
    compilation = compile_source(
        Source(
            FIXED
            + "let null = mean_difference_at_most(model=study, value=0)\n"
            + "let a = t_test(design=plan, null=null, alpha=1/20)\n"
        )
    )
    message = compilation.diagnostics[0].message
    assert "t_test_one_sided takes mean_difference_at_most" in message


def test_study_report_gives_statuses_and_one_assumption_table():
    from statclaim.contract_reports import report_markdown, study_report

    report = study_report(compile_source(Source(MIXED)), "mixed_endpoints.stat")
    by_name = {
        claim["names"][0] if claim["names"] else claim["kind"]: claim for claim in report["claims"]
    }
    statuses = sorted(claim["best_status"] for claim in report["claims"])
    assert statuses == ["conditional", "verified"]
    register = {item["id"] or item["text"]: item for item in report["assumption_register"]}
    assert register["normal_outcomes"]["status"] == "assumed"
    assert register["prespecified_family"]["status"] == "declared"
    assert register["member_guarantee:symptoms"]["kind"] == "member"
    assert all(item["needed_by"] for item in register.values())
    text = report_markdown(report)
    assert "## Evidence each claim can receive" in text
    assert "conditional: combination proved in Lean; members assumed" in text
    assert "| Assumption | Kind | Status | Needed by |" in text
    assert by_name


LOOKS = (
    "use models.two_arm_continuous\nuse sampling\nuse tests.t\nuse designs.group_sequential\n"
    "let halfway = two_arm_continuous(n_control=50, n_treatment=50)\n"
    "let complete = two_arm_continuous(n_control=100, n_treatment=100)\n"
    "let interim = t_test(design=fixed(model=halfway), null=equal_means(model=halfway), "
    "alpha=1/200)\n"
    "let final = t_test(design=fixed(model=complete), null=equal_means(model=complete), "
    "alpha=9/200)\n"
)
TRIAL = LOOKS + "let trial = alpha_spending(looks=[interim, final], alpha=1/20)\n"


def test_sequential_looks_bound_the_one_null_and_replace_run_once():
    record = family_derivation(TRIAL, "trial")
    assert check_derivation(record) == []
    assert record["contract"] == "designs.group_sequential/alpha_spending"
    guarantee = record["guarantee"]
    assert guarantee["quantity"] == "type_I_error" and guarantee["bound"] == "1/20"
    assert guarantee["null"] == "mean_treatment = mean_control"
    assert guarantee["given"][0] == "prespecified_looks"
    # Looking twice is what the design accounts for, so "run once" is not assumed.
    assert not any("run once" in text for text in record["assumptions"])
    assert any("stops at the first look" in text for text in record["assumptions"])
    claim = compile_source(Source(TRIAL + "verify typeI(trial)\n")).program.requests[0].claim
    assert claim.kind == "typeI" and claim.guarantee.quantity == "type_I_error"


@pytest.mark.parametrize(
    "tail,code",
    [
        ("let trial = alpha_spending(looks=[final, interim], alpha=1/20)\n", "sequential_order"),
        (
            "let other = welch_test(design=fixed(model=complete), "
            "null=equal_means(model=complete), alpha=9/200)\n"
            "let trial = alpha_spending(looks=[interim, other], alpha=1/20)\n",
            "sequential_question",
        ),
        (
            "let shifted = t_test_one_sided(design=fixed(model=complete), "
            "null=mean_difference_at_most(model=complete, value=0), alpha=9/200)\n"
            "let trial = alpha_spending(looks=[interim, shifted], alpha=1/20)\n",
            "sequential_question",
        ),
        ("let trial = alpha_spending(looks=[interim], alpha=1/20)\n", "family_size"),
        (
            "use multiplicity.bonferroni\n"
            "let trial = alpha_spending(looks=[interim, final], alpha=1/20)\n"
            "let wrong = familywise(trial)\n",
            "type",
        ),
    ],
)
def test_sequential_design_mistakes_are_explained(tail, code):
    assert codes(LOOKS + tail) == [code]


def test_overspending_across_looks_stays_unresolved():
    text = TRIAL.replace("alpha=9/200", "alpha=1/20") + "verify typeI(trial)\n"
    assert codes(text) == ["allocation"]
    record = family_derivation(TRIAL.replace("alpha=9/200", "alpha=1/20"), "trial")
    assert check_derivation(record) == [] and record["guarantee"] is None


@pytest.mark.parametrize(
    "change",
    [
        lambda d: d["subject"].update(method="bonferroni"),
        lambda d: d["subject"]["analyses"].reverse(),
        lambda d: d["subject"]["analyses"][1]["analysis"].update(test="welch_test"),
        lambda d: d["guarantee"].update(quantity="familywise_error"),
        lambda d: d["assumptions"].append("The test is run once, on the complete data."),
        lambda d: d["steps"][13]["facts"].update(sizes=[[1, 1], [2, 2]]),
    ],
)
def test_checker_rejects_an_altered_sequential_design(change):
    record = family_derivation(TRIAL, "trial")
    change(record)
    assert check_derivation(record)


def test_exact_one_sided_and_margin_tests_can_join_a_family():
    text = (
        "use models.two_arm_binomial\nuse sampling\nuse tests.fisher\nuse tests.difference\n"
        "use multiplicity.bonferroni\n"
        "let study = two_arm_binomial(n_control=40, n_treatment=40)\n"
        "let plan = fixed(model=study)\n"
        "let better = fisher_one_sided(design=plan, "
        "null=proportion_difference_at_most(model=study, value=0), alpha=1/40)\n"
        "let not_worse = difference_test(design=plan, "
        "null=proportion_difference_at_most(model=study, value=-1/10), alpha=1/40)\n"
        "let endpoints = bonferroni(analyses=[better, not_worse], alpha=1/20)\n"
    )
    record = family_derivation(text)
    assert check_derivation(record) == []
    assert [m["basis"] for m in record["guarantee"]["members"]] == [
        "tests.fisher/fisher_one_sided",
        "tests.difference/difference_test",
    ]
    assert all(m["grade"] == "proved" for m in record["guarantee"]["members"])


@pytest.mark.parametrize("path", sorted((ROOT / "examples").rglob("*.stat")), ids=lambda p: p.stem)
def test_every_assumption_a_claim_reports_has_an_id_and_kind(path):
    """A new module must classify its assumption sentences in methods/identify.py."""
    from statclaim.language_inspection import inspect_program

    compilation = compile_source(Source(path.read_text(), str(path)))
    if compilation.status == "invalid":
        return
    for claim in inspect_program(compilation):
        for item in claim["identified_assumptions"]:
            assert item["id"] and item["kind"], item["text"]
            assert item["status"] in ("declared", "assumed", "condition")


CONFIRMATORY = (ROOT / "examples/confirmatory_trial.stat").read_text()
SEQUENCE = (
    TWO_MEANS.replace("alpha=1/40", "alpha=1/20").replace(
        "use multiplicity.bonferroni", "use multiplicity.fixed_sequence"
    )
    + "let endpoints = fixed_sequence(analyses=[first, second], alpha=1/20)\n"
)


def test_fixed_sequence_tests_each_endpoint_at_the_full_level():
    record = family_derivation(SEQUENCE)
    assert check_derivation(record) == []
    assert record["contract"] == "multiplicity.fixed_sequence/fixed_sequence"
    guarantee = record["guarantee"]
    assert guarantee["quantity"] == "familywise_error" and guarantee["bound"] == "1/20"
    assert guarantee["given"][0] == "prespecified_order"
    # No allocation rule applies: the order, not a split, controls the error.
    assert "allocation" not in [step["rule"] for step in record["steps"]]
    assert "full-level" in [step["rule"] for step in record["steps"]]
    assert codes(
        SEQUENCE.replace("[first, second], alpha=1/20", "[first, second], alpha=1/40")
    ) == ["sequence_level"]


def test_a_design_with_looks_can_be_a_member_of_a_sequence_or_family():
    record = family_derivation(CONFIRMATORY, "hierarchy")
    assert check_derivation(record) == []
    members = record["guarantee"]["members"]
    assert [m["grade"] for m in members] == ["conditional", "cited", "proved"]
    assert members[0]["basis"] == "designs.group_sequential/alpha_spending"
    assert record["guarantee"]["scope"] == "asymptotic"
    rules = [step["rule"] for step in record["steps"]]
    assert rules.count("sequential-contract") == 1
    assert rules.count("fixed-sequence-contract") == 1
    assert rules.index("sequential-contract") < rules.index("fixed-sequence-contract")
    # The nested design's own split is an obligation of the whole.
    over = CONFIRMATORY.replace("alpha=9/200", "alpha=1/20")
    assert codes(over).count("allocation") == 2  # asked for twice: hierarchy and survival
    nested = family_derivation(over, "hierarchy")
    assert check_derivation(nested) == [] and nested["guarantee"] is None
    # Looks themselves cannot hold designs.
    assert codes(
        CONFIRMATORY + "let wrong = alpha_spending(looks=[survival, symptoms], alpha=1/20)\n"
    ) == ["type"]


@pytest.mark.parametrize(
    "change",
    [
        lambda d: d["subject"].update(method="bonferroni"),
        lambda d: d["subject"]["analyses"][1]["analysis"].update(alpha="1/40"),
        lambda d: d["subject"]["analyses"][0]["analysis"]["analyses"].reverse(),
        lambda d: d["subject"]["analyses"][0]["analysis"].update(method="bonferroni"),
        lambda d: d["guarantee"]["members"][0].update(grade="proved"),
        lambda d: d["guarantee"].update(scope="finite_sample"),
        lambda d: d["assumptions"].pop(4),
    ],
)
def test_checker_rejects_an_altered_nested_design(change):
    record = family_derivation(CONFIRMATORY, "hierarchy")
    change(record)
    assert check_derivation(record)


def test_report_lists_the_assumptions_of_every_level_of_a_nested_design():
    from statclaim.contract_reports import study_report

    report = study_report(compile_source(Source(CONFIRMATORY)), "confirmatory_trial.stat")
    register = {item["id"]: item for item in report["assumption_register"]}
    for expected in (
        "prespecified_order",
        "prespecified_looks",
        "member_guarantee:survival",
        "member_guarantee:interim",
        "independent_censoring",
        "normal_outcomes",
    ):
        assert expected in register
    assert "familywise(hierarchy)" in register["independent_censoring"]["needed_by"]
