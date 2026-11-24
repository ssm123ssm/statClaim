"""Explanations, study reports and change-impact analysis built on derivations.

Nothing here runs a calculation or Lean; `lean_report.py` adds the Lean section a report
shows when asked. Every derivation shown has been passed through the independent checker
first, and the result of that check is shown.
"""

from statclaim.derivation_checker import check_derivation
from statclaim.language import normalize
from statclaim.language_compiler import Compilation
from statclaim.language_inspection import inspect_program
from statclaim.methods.identify import identify


def explain(compilation: Compilation, name: str | None = None) -> list[dict]:
    """Checked derivations for the whole file, or for one named declaration."""
    entries = []
    for derivation in compilation.derivations:
        if name is not None and derivation.name != name:
            continue
        record = derivation.to_dict()
        problems = check_derivation(record)
        binding = next(b for b in compilation.program.bindings if b.name == derivation.name)
        entries.append(
            {
                "name": derivation.name,
                "source": binding.span.to_dict(),
                "checked": not problems,
                "problems": problems,
                "derivation": record,
            }
        )
    return entries


def _facts(facts: dict) -> str:
    def show(value) -> str:
        if isinstance(value, dict):
            return ", ".join(f"{key} {item}" for key, item in value.items())
        if isinstance(value, list):
            return ", ".join(str(item) for item in value)
        return str(value)

    shown = {key: value for key, value in facts.items() if key not in ("subject", "statement")}
    return "; ".join(f"{key.replace('_', ' ')}: {show(value)}" for key, value in shown.items())


def explanation_markdown(entry: dict) -> str:
    derivation = entry["derivation"]
    lines = [
        f"## Contract for `{entry['name']}`",
        "",
        f"**Contract:** `{derivation['contract']}`",
        "",
        f"**Conclusion:** {derivation['conclusion']}",
        "",
        "### Why it passed",
        "",
    ]
    for index, step in enumerate(derivation["steps"], 1):
        based = (
            f" (from steps {', '.join(str(use + 1) for use in step['uses'])})"
            if step["uses"]
            else ""
        )
        facts = _facts(step["facts"])
        lines.append(f"{index}. **{step['rule']}**{based}: {step['conclusion']}")
        lines.append(f"   - Rule: {step['premise']}")
        if facts and not step["uses"]:
            lines.append(f"   - Facts: {facts}")
    guarantee = derivation.get("guarantee")
    if guarantee:
        lines += ["", "### Guarantee, given the assumptions", "", guarantee["sentence"], ""]
        if guarantee["grade"] == "conditional":
            lines.append(
                "This follows from the members' own error bounds, which are assumed. "
                "Lean checks the combination when you verify the familywise claim."
            )
        else:
            method = guarantee["method"]
            lines += [
                f"Declared by the author as: {method['title']}. StatClaim has no contract "
                "or source for this test and checked nothing about its guarantee."
                if guarantee["grade"] == "declared"
                else f"Cited from {method['title']} (`{method['key']}`, version "
                f"{method['version']}); not proved in Lean.",
                "",
            ]
            lines += [f"- {reference}" for reference in guarantee["references"]]
    lines += ["", "### Assumptions you must meet in the real study", ""]
    lines += [f"- {assumption}" for assumption in derivation["assumptions"]]
    lines += ["", "### Unresolved obligations", ""]
    if derivation["obligations"]:
        lines += [f"- `{item['code']}`: {item['statement']}" for item in derivation["obligations"]]
    else:
        lines.append("None.")
    lines += ["", "### Not established here", "", derivation["not_established"], ""]
    if entry["checked"]:
        lines.append("Independent check of this derivation: passed.")
    else:
        lines.append("Independent check of this derivation: **failed**.")
        lines += [f"- {problem}" for problem in entry["problems"]]
    return "\n".join(lines)


def assumption_register(claims: list[dict]) -> list[dict]:
    """Every assumption the requested claims rest on, once, with the claims that need it.

    Cited and conditional claims supply ids and kinds. Other claims supply text only.
    """
    register: dict[str, dict] = {}
    for claim in claims:
        label = ", ".join(claim["names"]) or f"{claim['kind']}({claim['claim']['subject_name']})"
        identified = claim["identified_assumptions"]
        entries = identified or [
            {"id": None, "kind": None, "text": text, "status": "assumed"}
            for text in claim["assumptions"]
        ]
        for entry in entries:
            item = register.setdefault(
                entry["id"] or entry["text"],
                {
                    "id": entry["id"],
                    "kind": entry["kind"],
                    "text": entry["text"],
                    "status": entry["status"],
                    "needed_by": [],
                },
            )
            if label not in item["needed_by"]:
                item["needed_by"].append(label)
    return list(register.values())


STATUS_MEANING = {
    "verified": "proved in Lean",
    "conditional": "combination proved in Lean; members assumed",
    "cited": "cited from the literature; not machine-checked",
    "declared": "declared by the author; not checked and not cited",
    "calculated": "calculated only: an approximation, never verified",
}


def study_report(compilation: Compilation, path: str) -> dict:
    """Validated contracts, requested claims, assumptions and open obligations."""
    contracts = explain(compilation)
    claims = inspect_program(compilation)
    assumptions = list(
        dict.fromkeys(
            assumption for entry in contracts for assumption in entry["derivation"]["assumptions"]
        )
    )
    obligations = [
        {"contract": entry["name"], **item}
        for entry in contracts
        for item in entry["derivation"]["obligations"]
    ]
    return {
        "schema_version": 1,
        "source": path,
        "status": compilation.status,
        "contracts": contracts,
        "claims": [
            {
                "names": claim["names"],
                "kind": claim["kind"],
                "label": ", ".join(claim["names"])
                or f"{claim['kind']}({claim['claim']['subject_name']})",
                "description": claim["description"],
                "scope": claim["scope"],
                "best_status": claim["best_status"],
                "weakest_link": claim["weakest_link"],
                "guarantee": claim["guarantee"],
                "assumptions": claim["assumptions"],
                "requirements": claim["requirements"],
                "verification_requested": any(
                    request["operation"] == "verify" for request in claim["requests"]
                ),
            }
            for claim in claims
        ],
        "assumptions": assumptions,
        "assumption_register": assumption_register(claims),
        "obligations": obligations,
        "diagnostics": [diagnostic.to_dict() for diagnostic in compilation.diagnostics],
        "all_derivations_checked": all(entry["checked"] for entry in contracts),
    }


def report_markdown(report: dict) -> str:
    lines = [
        "# Study contract report",
        "",
        f"Source: `{report['source']}`",
        "",
        f"Compilation status: `{report['status']}`",
        "",
        "This report covers compatibility of the declarations, which the Lean check below "
        "proves as Lean states them. The other sections are Python's reading, not proofs."
        if report.get("lean", {}).get("status") == "checked"
        else "This report covers compatibility of the declarations. It is not a proof of any "
        "statistical guarantee. Claims below are established only by `verify(...)`.",
        "",
        "Even a verified claim concerns the study as declared in this file, under the "
        "listed assumptions. It says nothing about how the study is run: an endpoint chosen "
        "after seeing data, participants excluded after randomisation, or repeated "
        "measurements counted as separate participants are invisible unless declared.",
        "",
    ]
    if "lean" in report:
        lines += lean_markdown(report["lean"])
    lines += [
        "## Summary",
        "",
        "| Declaration | Contract | Unresolved obligations | Independently checked |",
        "| --- | --- | --- | --- |",
    ]
    for entry in report["contracts"]:
        derivation = entry["derivation"]
        lines.append(
            f"| `{entry['name']}` | `{derivation['contract']}` | "
            f"{len(derivation['obligations'])} | {'yes' if entry['checked'] else 'NO'} |"
        )
    if not report["contracts"]:
        lines.append("| (none) | | | |")
    lines += [
        "",
        "## Evidence each claim can receive",
        "",
        "The strongest status `verify(...)` can give each claim. Nothing was run for this report.",
        "",
        "| Claim | Kind | Best status | Weakest part | Exact or approximate |",
        "| --- | --- | --- | --- | --- |",
    ]
    for claim in report["claims"]:
        names = f"`{claim['label']}`"
        scope = (
            "exact at the declared size"
            if claim["scope"] == "finite_sample"
            else ("large-sample approximation")
        )
        lines.append(
            f"| {names} | {claim['kind']} | {claim['best_status']}: "
            f"{STATUS_MEANING[claim['best_status']]} | {claim['weakest_link']['grade']}: "
            f"{', '.join(claim['weakest_link']['parts'])} | {scope} |"
        )
    if not report["claims"]:
        lines.append("| (none) | | | | |")
    lines += ["", "## Assumptions to meet in the real study", ""]
    if report["assumption_register"]:
        lines += [
            "Declared: stated by this file. Assumed: nothing in the file can show it. "
            "Condition: says what the claim is about.",
            "",
            "| Assumption | Kind | Status | Needed by |",
            "| --- | --- | --- | --- |",
        ]
        lines += [
            f"| {item['text']} | {item['kind'] or 'unclassified'} | {item['status']} | "
            f"{', '.join(item['needed_by'])} |"
            for item in report["assumption_register"]
        ]
    # A declaration's assumption is already listed if a claim reports the same one,
    # by text or by id, since modules word the same assumption slightly differently.
    listed = {item["text"] for item in report["assumption_register"]} | {
        item["id"] for item in report["assumption_register"]
    }
    extra = [
        text
        for text in report["assumptions"]
        if text not in listed and identify(text)["id"] not in listed
    ]
    if extra:
        lines += ["", "For declarations with no requested claim:", ""]
        lines += [f"- {assumption}" for assumption in extra]
    if not report["assumption_register"] and not extra:
        lines.append("None recorded.")
    lines += ["", "## Outstanding obligations", ""]
    lines += [
        f"- `{item['contract']}` / `{item['code']}`: {item['statement']}"
        for item in report["obligations"]
    ] or ["None."]
    if report["diagnostics"]:
        lines += ["", "## Diagnostics", ""]
        lines += [
            f"- {item['severity']} `{item['code']}` (line {item['source']['line']}): "
            + item["message"].splitlines()[0]
            for item in report["diagnostics"]
        ]
    lines += ["", "## Requested claims", ""]
    for claim in report["claims"]:
        names = ", ".join(f"`{name}`" for name in claim["names"]) or "(unnamed)"
        state = "verification requested" if claim["verification_requested"] else "not verified"
        lines.append(f"- {names} ({claim['kind']}, {state}): {claim['description']}")
    if not report["claims"]:
        lines.append("None.")
    lines += ["", "## Justifications", ""]
    for entry in report["contracts"]:
        lines += [explanation_markdown(entry), ""]
    return "\n".join(lines).rstrip() + "\n"


GRADE_WORDS = {
    "proved": "uses no premise",
    "conditional": "proved from its members' premises",
    "cited": "rests on its cited premise",
    "declared": "rests on the author's declared premise",
}


def lean_markdown(lean: dict) -> list[str]:
    """The report's Lean section (`lean_report.lean_check`)."""
    lines = ["## Lean check", ""]
    if lean["status"] != "checked":
        return [*lines, lean["message"], ""]
    facts, claims = len(lean["contract_facts"]), lean["claims"]
    where = (
        f"Certificate `{lean['certificate_id'][:12]}` is in "
        f"`{lean['certificate_directory']}`; `statclaim check-certificate` replays it."
    )
    if lean.get("semantics"):
        lines += [
            "Lean checked this program through the StatClaim semantics: the contracts of its "
            f"{facts} declared tests and combinations hold, and each claim below follows, by "
            "the soundness theorem, from the premises of the tests it involves. Lean's grade "
            f"comes from those premises. {where}",
            "",
        ]
    else:
        lines += [
            f"Lean checked this program: its {facts} contract facts hold, and each claim "
            "below follows from the premises its proof uses. Lean's grade comes from those "
            f"premises. {where}",
            "",
        ]
    if claims:
        lines += ["| Claim | Line | Lean | Python |", "| --- | --- | --- | --- |"]
        lines += [
            f"| `{c['claim']}` | {c['source']['line']} | {c['grade']}: "
            f"{GRADE_WORDS[c['grade']]} | {c['python']} |"
            for c in claims
        ]
        lines.append("")
        if any(c["grade"] != c["python"] for c in claims):
            lines += [
                "Where the two differ, Lean's grade stands: Python grades a combination by "
                "assuming its members, while Lean proves the members it can.",
                "",
            ]
    if lean["premises"]:
        lines += ["Premises: " + ", ".join(f"`{name}`" for name in lean["premises"]) + ".", ""]
    if lean["refuted"] and lean.get("semantics"):
        lines += [
            f"- `{claim}`: its design stops by a rule that depends on the data, so it supplies "
            "no sampling law; the semantics states the claim as False, and nothing proves it."
            for claim in lean["refuted"]
        ]
        lines.append("")
    elif lean["refuted"]:
        lines += [
            f"- `{holder}`: Lean proves its design supplies no sampling law (`{theorem}`), "
            "so no claim is stated."
            for holder, theorem in lean["refuted"].items()
        ]
        lines.append("")
    others = {k: v for k, v in lean["not_translated"].items() if k not in lean["refuted"]}
    if others:
        lines += ["Not in Lean yet:", ""]
        lines += [f"- `{name}`: {reason}" for name, reason in others.items()]
        lines.append("")
    return lines


def _contract_state(entry: dict | None) -> str:
    if entry is None:
        return "no contract"
    count = len(entry["derivation"]["obligations"])
    return "satisfied" if not count else f"satisfied, {count} unresolved"


def impact(old: Compilation, new: Compilation) -> dict:
    """Which declarations, contracts and claims a change affects.

    Derivations are recomputed for both versions and compared. A declaration is
    changed directly when its own value differs and nothing it depends on
    changed; otherwise it is affected through a dependency.
    """
    before = {binding.name: binding for binding in old.program.bindings}
    after = {binding.name: binding for binding in new.program.bindings}
    differing = {
        name
        for name in before.keys() & after.keys()
        if normalize(before[name].value) != normalize(after[name].value)
    }
    added, removed = after.keys() - before.keys(), before.keys() - after.keys()
    touched = differing | added | removed
    changes = []
    for name in [*after, *(name for name in before if name not in after)]:
        if name not in touched:
            continue
        if name in removed:
            kind = "removed or no longer valid"
        elif name in added:
            kind = "added"
        elif any(dependency in touched for dependency in after[name].dependencies):
            kind = "affected through a dependency"
        else:
            kind = "changed directly"
        changes.append({"name": name, "change": kind})
    old_contracts = {entry["name"]: entry for entry in explain(old)}
    new_contracts = {entry["name"]: entry for entry in explain(new)}
    contracts = []
    for name in [*new_contracts, *(name for name in old_contracts if name not in new_contracts)]:
        previous, current = old_contracts.get(name), new_contracts.get(name)
        same = (
            previous is not None
            and current is not None
            and previous["derivation"] == current["derivation"]
        )
        if same:
            continue
        now = _contract_state(current)
        if current is not None and now == _contract_state(previous):
            now += " (re-derived for the new declaration)"
        contracts.append(
            {
                "name": name,
                "before": _contract_state(previous),
                "after": now,
                "checked": current["checked"] if current else None,
            }
        )

    def claim_key(request) -> tuple:
        return (request.operation, request.claim.kind, request.claim.name)

    old_claims = {claim_key(r): normalize(r.claim) for r in old.program.requests}
    new_claims = {claim_key(r): normalize(r.claim) for r in new.program.requests}
    claims = []
    for key in [*new_claims, *(key for key in old_claims if key not in new_claims)]:
        if old_claims.get(key) == new_claims.get(key):
            continue
        state = "added" if key not in old_claims else "removed" if key not in new_claims else None
        claims.append(
            {
                "operation": key[0],
                "claim": key[1],
                "subject": key[2],
                "change": state or "must be re-run: its subject changed",
            }
        )
    return {
        "schema_version": 1,
        "status_before": old.status,
        "status_after": new.status,
        "declarations": changes,
        "contracts": contracts,
        "claims": claims,
        "new_diagnostics": [
            diagnostic.to_dict()
            for diagnostic in new.diagnostics
            if diagnostic.to_dict() not in [d.to_dict() for d in old.diagnostics]
        ],
    }


def impact_markdown(result: dict) -> str:
    lines = [
        "# Change impact",
        "",
        f"Status: `{result['status_before']}` → `{result['status_after']}`",
        "",
        "## Declarations",
        "",
    ]
    lines += [f"- `{item['name']}`: {item['change']}" for item in result["declarations"]] or [
        "No declaration changed."
    ]
    lines += ["", "## Contracts affected", ""]
    lines += [
        f"- `{item['name']}`: {item['before']} → {item['after']}" for item in result["contracts"]
    ] or ["None."]
    lines += ["", "## Claims affected", ""]
    lines += [
        f"- `{item['operation']} {item['claim']}({item['subject']})`: {item['change']}"
        for item in result["claims"]
    ] or ["None."]
    if result["new_diagnostics"]:
        lines += ["", "## New diagnostics", ""]
        lines += [
            f"- {item['severity']} `{item['code']}` (line {item['source']['line']}): "
            + item["message"].splitlines()[0]
            for item in result["new_diagnostics"]
        ]
    lines += [
        "",
        "Earlier certificates refer to the earlier declarations. Re-run verification for "
        "every affected claim.",
    ]
    return "\n".join(lines) + "\n"
