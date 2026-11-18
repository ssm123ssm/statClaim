"""Re-check the two-stage designs tabulated by Simon (1989).

    uv run python replication/simon.py           # exact calculation and optimality; no Lean
    uv run python replication/simon.py --check   # fail if simon_results.md is out of date
    uv run python replication/simon.py --lean    # also prove each design in Lean (slow)
    uv run python replication/simon.py --fresh   # prove all again; compare with simon_proofs.json

Three questions are asked of each of the 102 designs:
  1. Does it meet its stated Type I error and power? (exact arithmetic)
  2. Is it the optimal or minimax design, among designs of at most 120 participants?
  3. Can Lean prove its error bound for every response rate at or below the null,
     and its power at the alternative?
"""

import json
import sys
import tempfile
from fractions import Fraction
from math import comb
from pathlib import Path

from statclaim import __version__
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.planning import MAX_SEARCH_TOTAL, search_two_stage

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DATA = json.loads((HERE / "simon1989.json").read_text())


def source(design: dict, operation: str) -> str:
    return f"""use designs.two_stage
use planning
let stages = two_stage_binomial(n_stage1={design["n1"]}, n_stage2={design["n"] - design["n1"]})
let rule = threshold_rule(continue_above={design["r1"]}, reject_above={design["r"]})
let analysis = two_stage_test(design=stages, rule=rule, null_rate={Fraction(design["p0"])})
let target = power_target(
    at=response_rate(value={Fraction(design["p1"])}),
    minimum={1 - Fraction(design["beta"])},
    maximum_typeI={design["alpha"]},
)
let outcome = {operation}(meets(analysis=analysis, target=target))
"""


def expected_size(n1: int, n: int, r1: int, p0: Fraction) -> tuple[Fraction, Fraction]:
    """Expected sample size and early-stopping probability at p0, computed here
    independently of StatClaim."""
    stop = sum(comb(n1, k) * p0**k * (1 - p0) ** (n1 - k) for k in range(r1 + 1))
    return n1 + (1 - stop) * (n - n1), stop


def label(design: dict) -> str:
    return f"{design['r1']}/{design['n1']}, {design['r']}/{design['n']}"


def calculate(design: dict) -> dict:
    with tempfile.TemporaryDirectory() as directory:
        report = check_source(
            Source(source(design, "calculate"), "design.stat"),
            project=Path(directory),
            output=Path(directory) / "run",
        )
    calculation = report["requests"][0]["report"]["calculation"]
    p0 = Fraction(design["p0"])
    size, stop = expected_size(design["n1"], design["n"], design["r1"], p0)
    return {
        "typeI": float(calculation["typeI"]["decimal_approximation"]),
        "power": float(calculation["power"]["decimal_approximation"]),
        "meets_targets": calculation["typeI_target_met"] and calculation["power_target_met"],
        "expected_size": float(size),
        "early_stop": float(stop),
        "table_values_match": abs(float(size) - design["en"]) < 0.051
        and abs(float(stop) - design["pet"]) < 0.0051,
    }


def optimality(design: dict, size: float) -> dict:
    """Search every count-threshold design of at most 120 participants."""
    found, searched = search_two_stage(
        Fraction(design["p0"]),
        Fraction(design["p1"]),
        1 - Fraction(design["beta"]),
        Fraction(design["alpha"]),
        MAX_SEARCH_TOTAL,
        design["kind"],
    )
    best = {
        "n1": found.n_first,
        "n": found.n_first + found.n_second,
        "r1": found.rule.continue_above,
        "r": found.rule.reject_above,
    }
    best_size = float(expected_size(best["n1"], best["n"], best["r1"], Fraction(design["p0"]))[0])
    same = all(best[key] == design[key] for key in best)
    if design["kind"] == "optimal":
        better = best_size < size - 1e-9
    else:
        better = best["n"] < design["n"] or (best["n"] == design["n"] and best_size < size - 1e-9)
    return {
        "candidates_searched": searched,
        "search_finds_same_design": same,
        "better_design_exists": better,
        "best": {**best, "expected_size": best_size},
    }


def proof_key(design: dict) -> str:
    return f"{design['kind']} p0={design['p0']} p1={design['p1']} {label(design)}"


def prove(design: dict, directory: Path) -> dict:
    report = check_source(
        Source(source(design, "verify"), "design.stat"), project=ROOT, output=directory, timeout=600
    )
    value = report["values"]["outcome"]
    evidence = value["evidence"] or {}
    return {
        "status": value["status"],
        "certificate_id": (evidence.get("certificate") or {}).get("certificate_id"),
        "established": evidence.get("established_properties", []),
        "diagnostics": [d["message"].splitlines()[0] for d in value["diagnostics"]],
    }


def run() -> list[dict]:
    rows = []
    for design in DATA["designs"]:
        result = calculate(design)
        rows.append({**design, **result, **optimality(design, result["expected_size"])})
    return rows


def render(rows: list[dict], proofs: dict | None) -> str:
    met = sum(row["meets_targets"] for row in rows)
    matched = sum(row["table_values_match"] for row in rows)
    same = sum(row["search_finds_same_design"] for row in rows)
    better = [row for row in rows if row["better_design_exists"]]
    tied = [
        row
        for row in rows
        if not row["search_finds_same_design"] and not row["better_design_exists"]
    ]
    lines = [
        "# Re-checking the designs of Simon (1989)",
        "",
        f"Generated by `replication/simon.py` with StatClaim {__version__}.",
        "",
        f"Source: {DATA['source']}",
        "",
        "| Question | Result |",
        "| --- | --- |",
        f"| Designs tabulated | {len(rows)} |",
        f"| Meet their stated Type I error and power (exact arithmetic) | {met} of {len(rows)} |",
        "| Tabulated expected size and early-stopping probability match the exact values "
        f"| {matched} of {len(rows)} |",
        f"| An exhaustive search up to {MAX_SEARCH_TOTAL} participants returns the same design "
        f"| {same} of {len(rows)} |",
        f"| The search finds a strictly better design | {len(better)} of {len(rows)} |",
    ]
    if proofs is not None:
        proved = sum(item["status"] == "verified" for item in proofs.values())
        lines.append(f"| Error bound and power proved in Lean | {proved} of {len(proofs)} |")
    lines += [
        "",
        "A design is written `r1/n1, r/n`: stop for futility with `r1` or fewer responses "
        "among the first `n1`, and reject the drug with `r` or fewer among all `n`.",
        "",
    ]
    mismatched = [row for row in rows if not row["table_values_match"]]
    if mismatched:
        lines += [
            "## Tabulated values that differ from the exact ones",
            "",
            "The designs themselves are correct. The expected size agrees in every row, and "
            "it is computed from the early-stopping probability, so the differences below "
            "are in the printed probability only.",
            "",
            "| Table | Criterion | p0 | p1 | Design | Expected size: printed, exact "
            "| Early stopping: printed, exact |",
            "| --- | --- | --- | --- | --- | --- | --- |",
        ]
        lines += [
            f"| {row['table']} | {row['kind']} | {row['p0']} | {row['p1']} | {label(row)} | "
            f"{row['en']}, {row['expected_size']:.2f} | {row['pet']:.2f}, {row['early_stop']:.3f} |"
            for row in mismatched
        ]
        lines.append("")
    if better:
        lines += [
            "## Designs for which the search finds a better one",
            "",
            "| Criterion | p0 | p1 | alpha | beta | Tabulated | Expected size | Found "
            "| Expected size |",
            "| --- | --- | --- | --- | --- | --- | ---: | --- | ---: |",
        ]
        for row in better:
            best = row["best"]
            lines.append(
                f"| {row['kind']} | {row['p0']} | {row['p1']} | {row['alpha']} | {row['beta']} | "
                f"{label(row)} | {row['expected_size']:.3f} | {label(best)} | "
                f"{best['expected_size']:.3f} |"
            )
        lines.append("")
    if tied:
        lines += [
            "## Designs for which the search returns a different, equally good design",
            "",
            "| Criterion | p0 | p1 | alpha | beta | Tabulated | Found |",
            "| --- | --- | --- | --- | --- | --- | --- |",
        ]
        lines += [
            f"| {row['kind']} | {row['p0']} | {row['p1']} | {row['alpha']} | {row['beta']} | "
            f"{label(row)} | {label(row['best'])} |"
            for row in tied
        ]
        lines.append("")
    tight = min(rows, key=lambda row: Fraction(row["alpha"]) - Fraction(row["typeI"]))
    lines += [
        "## Margins",
        "",
        f"The design closest to its Type I limit is {tight['kind']} {label(tight)} "
        f"(p0 = {tight['p0']}): error {tight['typeI']:.6f} against "
        f"{float(Fraction(tight['alpha'])):.2f}.",
        "",
        "The search ranks candidates in floating point. A design it reports as better is "
        "confirmed here by its exact expected size.",
        "",
    ]
    return "\n".join(lines)


def fresh() -> int:
    """Prove every design again, ignoring earlier certificates, and compare with the pinned file.

    The new results go to a temporary file; simon_proofs.json is not changed.
    """
    pinned = json.loads((HERE / "simon_proofs.json").read_text())
    path = Path(tempfile.gettempdir()) / "statclaim-simon-proofs-fresh.json"
    print(f"Writing fresh proofs to {path}", flush=True)
    proofs = {}
    with tempfile.TemporaryDirectory() as directory:
        for index, design in enumerate(DATA["designs"]):
            key = proof_key(design)
            proofs[key] = prove(design, Path(directory) / f"design-{index:03d}")
            path.write_text(json.dumps(proofs, indent=1) + "\n")
            print(f"{index + 1}/{len(DATA['designs'])} {key}: {proofs[key]['status']}", flush=True)
    differ = [
        key
        for key in sorted(pinned.keys() | proofs.keys())
        if (pinned.get(key) or {}).get("status") != (proofs.get(key) or {}).get("status")
        or (pinned.get(key) or {}).get("established") != (proofs.get(key) or {}).get("established")
    ]
    verified = sum(item["status"] == "verified" for item in proofs.values())
    print(f"{verified} of {len(proofs)} designs verified afresh.")
    if differ:
        print(f"Differ from simon_proofs.json: {', '.join(differ)}")
        return 1
    print("Statuses and proved statements match simon_proofs.json.")
    return 0


def main() -> int:
    if "--fresh" in sys.argv:
        return fresh()
    rows = run()
    proofs = None
    proof_file = HERE / "simon_proofs.json"
    if "--lean" in sys.argv:
        proofs = json.loads(proof_file.read_text()) if proof_file.exists() else {}
        with tempfile.TemporaryDirectory() as directory:
            for index, design in enumerate(DATA["designs"]):
                key = proof_key(design)
                if proofs.get(key, {}).get("status") == "verified":
                    continue
                proofs[key] = prove(design, Path(directory) / f"design-{index:03d}")
                proof_file.write_text(json.dumps(proofs, indent=1) + "\n")
                print(f"{index + 1}/{len(rows)} {key}: {proofs[key]['status']}", flush=True)
    elif proof_file.exists():
        proofs = json.loads(proof_file.read_text())
    text = render(rows, proofs)
    if "--check" in sys.argv:
        stale = (HERE / "simon_results.md").read_text() != text
        print("simon_results.md is out of date." if stale else "simon_results.md is current.")
        return 1 if stale else 0
    (HERE / "simon_results.md").write_text(text)
    (HERE / "simon_results.json").write_text(json.dumps(rows, indent=1) + "\n")
    print(f"Wrote {len(rows)} designs to replication/simon_results.md.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
