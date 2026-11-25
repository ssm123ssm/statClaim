"""The canonical program printed back as source compiles to the same program.

The printer reads the canonical record alone, so a round trip is a second reading of what the
compiler made of a file: a field the compiler misread, dropped or invented comes back changed.
"""

import json
import re
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from random import Random

import pytest

from statclaim.language import ProgramIR
from statclaim.language.registry import MODULES
from statclaim.language_compiler import compile_source
from statclaim.language_printer import Unprintable, program_source
from statclaim.language_syntax import Source

ROOT = Path(__file__).resolve().parents[1]
CORPUS = sorted(
    [
        *(ROOT / "examples").rglob("*.stat"),
        *(ROOT / "replication").glob("*/*.stat"),
        *(ROOT / "tests/fixtures").glob("*.stat"),
    ]
)

# Constructors no example uses, so the round trip covers every one.
EXTRA = """use models.two_arm_binomial
use models.two_arm_survival
use sampling
use tests.cluster
use tests.declared
use tests.survival
use designs.two_stage
use models.observational
use estimation.observational

let clinics = cluster_assignment(clusters_control=6, clusters_treatment=6, n_control=120, \
n_treatment=120)
let villages = two_arm(assignment=clinics, outcome=binary_outcome())
let responders = cluster_proportion_t_test(design=fixed(model=villages), \
null=equal_proportions(model=villages), alpha=1/20)
let arms = assignment(n_control=80, n_treatment=80, randomisation="complete")
let lifetimes = two_arm(assignment=arms, outcome=survival_outcome(better="higher"))
let ranked = log_rank(design=fixed(model=lifetimes), null=equal_survival(model=lifetimes), \
alpha=1/20)
let study = two_arm_binomial(n_control=50, n_treatment=50)
let shifted = declared_test(design=fixed(model=study), \
null=proportion_difference(model=study, value=1/10), alpha=1/20, \
method="A test of a shift in proportions")
let stages = two_stage_binomial(n_stage1=10, n_stage2=19)
let simon = two_stage_test(design=stages, rule=threshold_rule(continue_above=1, \
reject_above=5), null_rate=1/10)
let early = stopped_at_interim(analysis=simon, stage1_responses=1)
let sample = cross_sectional(n=400)
let counted = observed_table(model=sample, exposed_cases=30, exposed_noncases=70, \
unexposed_cases=40, unexposed_noncases=260)
verify typeI(responders)
verify typeI(ranked)
verify typeI(shifted)
verify two_stage_result(early)
verify prevalence_difference(table=counted, level=19/20)
"""


def compiled(text: str, path: str = "printed.stat"):
    return compile_source(Source(text, path))


def record(compilation) -> dict:
    """The canonical program without where each part was written."""
    program = json.loads(json.dumps(compilation.program.to_dict()))
    for binding in program["bindings"]:
        for key in ("source", "dependencies", "argument_sources"):
            del binding[key]
    for request in program["requests"]:
        del request["source"]
    return program


def programs() -> list[tuple[str, str]]:
    found = [(str(path.relative_to(ROOT)), path.read_text()) for path in CORPUS]
    return [*found, ("extra", EXTRA)]


COMPILED = [(name, text) for name, text in programs() if compiled(text).status != "invalid"]


def decimals(text: str) -> str:
    """Write every fraction with a finite decimal expansion as a decimal, outside strings."""

    def rewrite(match: re.Match) -> str:
        value = Fraction(int(match.group(1)), int(match.group(2)))
        denominator = value.denominator
        for factor in (2, 5):
            while denominator % factor == 0:
                denominator //= factor
        if denominator != 1:
            return match.group(0)
        written = format(Decimal(value.numerator) / Decimal(value.denominator), "f")
        return written if "." in written else f"{written}.0"

    parts = re.split(r'("(?:[^"\\]|\\.)*")', text)
    return "".join(
        part if part.startswith('"') else re.sub(r"(?<![\w.])(-?\d+)/(\d+)(?![\w.])", rewrite, part)
        for part in parts
    )


def assert_round_trip(text: str, name: str = "program.stat", **style) -> str:
    first = compiled(text, name)
    printed = program_source(first.program.to_dict(), **style)
    second = compiled(printed)
    assert second.status == first.status, (printed, second.diagnostics)
    assert record(second) == record(first), printed
    return printed


@pytest.mark.parametrize(("name", "text"), COMPILED, ids=[name for name, _ in COMPILED])
def test_every_program_prints_back_to_itself(name, text):
    printed = assert_round_trip(text, name)
    # Printing is stable: the printed program prints the same way.
    assert program_source(compiled(printed).program.to_dict()) == printed


@pytest.mark.parametrize(("name", "text"), COMPILED, ids=[name for name, _ in COMPILED])
def test_every_spelling_compiles_to_the_same_program(name, text):
    first = compiled(text, name)
    program = first.program.to_dict()
    for share in (True, False):
        for seed in (None, 7):
            printed = program_source(program, share=share, seed=seed)
            for spelling in (printed, decimals(printed)):
                again = compiled(spelling)
                assert again.status == first.status, spelling
                assert record(again) == record(first), spelling


@pytest.mark.parametrize("seed", range(4))
def test_programs_with_other_numbers_print_back_to_themselves(seed):
    """Change a number in an example at random: whatever still compiles round-trips."""
    draw = Random(seed)
    checked = 0
    for _ in range(100):
        _, text = draw.choice(COMPILED)
        numbers = [
            match
            for match in re.finditer(r"(?<![\w.\"])\d+(?:/\d+|\.\d+)?(?![\w.])", text)
            if "#" not in text[text.rfind("\n", 0, match.start()) + 1 : match.start()]
        ]
        match = draw.choice(numbers)
        old = Fraction(match.group(0))
        if old.denominator == 1:
            number = str(draw.randint(max(1, int(old) // 2), max(2, 2 * int(old))))
        else:
            denominator = draw.randint(2, 200)
            number = f"{draw.randint(1, denominator - 1)}/{denominator}"
        edited = text[: match.start()] + number + text[match.end() :]
        if compiled(edited).status != "invalid":
            assert_round_trip(edited)
            checked += 1
    assert checked >= 25


def test_every_constructor_is_printed_by_some_round_trip():
    used = set()
    for name, text in COMPILED:
        used |= set(re.findall(r"(\w+)\(", program_source(compiled(text, name).program.to_dict())))
    constructors = {c.name for module in MODULES.values() for c in module.constructors}
    assert constructors - used == set()


def test_a_compiler_that_misreads_a_field_fails_the_round_trip(monkeypatch):
    """A record with the arm sizes swapped prints as a file with them swapped, which a
    correct reading compiles back to the original: the two records differ."""
    text = (
        "use models.two_arm_binomial\nuse sampling\nuse tests.fisher\n"
        "let study = two_arm_binomial(n_control=40, n_treatment=60)\n"
        "let analysis = fisher(design=fixed(model=study), null=equal_proportions(model=study), "
        "alpha=1/20)\nverify typeI(analysis)\n"
    )
    to_dict = ProgramIR.to_dict

    def swap(value):
        if isinstance(value, dict):
            if "n_control" in value and "module" in value:
                value = {
                    **value,
                    "n_control": value["n_treatment"],
                    "n_treatment": value["n_control"],
                }
            return {key: swap(item) for key, item in value.items()}
        if isinstance(value, list):
            return [swap(item) for item in value]
        return value

    first = compiled(text)
    monkeypatch.setattr(ProgramIR, "to_dict", lambda self: swap(to_dict(self)))
    misread = compiled(text)
    printed = program_source(misread.program.to_dict())
    assert "n_control=60, n_treatment=40" in printed
    assert record(compiled(printed)) != record(misread)
    monkeypatch.undo()
    assert record(compiled(printed)) != record(first)


def test_a_record_no_constructor_writes_is_refused():
    program = compiled(EXTRA).program.to_dict()
    program["bindings"][0]["value"]["unknown"] = 1
    with pytest.raises(Unprintable, match="unknown"):
        program_source(program)


def test_compile_canonical_prints_the_program(capsys):
    from statclaim.cli import main

    path = ROOT / "examples/group_sequential.stat"
    assert main(["compile", "--canonical", str(path)]) == 0
    printed = capsys.readouterr().out
    assert 'spending="obrien_fleming"' in printed and "runs=10000" in printed
    assert record(compiled(printed)) == record(compiled(path.read_text(), str(path)))
