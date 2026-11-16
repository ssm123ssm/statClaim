"""Explanations, study reports and change-impact analysis built on derivations.

Nothing here runs a calculation or Lean. Every derivation shown has been passed
through the independent checker first, and the result of that check is shown.
"""

from statclaim.derivation_checker import check_derivation
from statclaim.language import normalize
from statclaim.language_compiler import Compilation
from statclaim.language_inspection import inspect_program


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
                "description": claim["description"],
                "assumptions": claim["assumptions"],
                "requirements": claim["requirements"],
                "verification_requested": any(
                    request["operation"] == "verify" for request in claim["requests"]
                ),
            }
            for claim in claims
        ],
        "assumptions": assumptions,
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
        "This report covers compatibility of the declarations. It is not a proof of any "
        "statistical guarantee. Claims below are established only by `verify(...)`.",
        "",
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
    lines += ["", "## Assumptions to meet in the real study", ""]
    lines += [f"- {assumption}" for assumption in report["assumptions"]] or ["None recorded."]
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
        after = _contract_state(current)
        if current is not None and after == _contract_state(previous):
            after += " (re-derived for the new declaration)"
        contracts.append(
            {
                "name": name,
                "before": _contract_state(previous),
                "after": after,
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
