"""How a claim's grade follows from the premises its proof uses. Trusted: see the trusted
base in docs/proposals/lean-translation.md.

Lean lists, for each claim, the fields of the program's `Premises` that its proof depends
on, following the program's own definitions and theorems (`collector`). The grade comes
from that list, never from how the proof was found: a proof that uses a cited premise
cannot be reported as proved. A premise's name starts with its kind, `cited_` or
`declared_`, as `denote.py` names it.
"""

from statclaim.lean_translation.emit import name as lean

# A member premise is an exact test's level, assumed inside a combination: it is proved on
# the test itself, as its own claim, but the combination is stated over the test seen from
# outside, so a combination resting on it is conditional.
ASSUMED = ("cited_", "declared_", "member_")


def grade(own: str | None, used: list[str]) -> str:
    """proved, conditional, cited or declared, from the premises a claim's proof uses.

    A claim resting on its own cited or declared premise has that grade. A combination
    resting on its members' cited or declared premises is conditional. A claim that uses
    no cited or declared premise is proved.
    """
    if own is not None and own in used:
        return "declared" if own.startswith("declared_") else "cited"
    if any(name.startswith(ASSUMED) for name in used):
        return "conditional"
    return "proved"


COLLECTOR = """\
-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [{pairs}] do
    let found ← IO.mkRef ({{}} : NameSet)
    let mut seen : NameSet := {{}}
    let mut stack := [claim]
    while !stack.isEmpty do
      let current := stack.head!
      stack := stack.tail!
      if seen.contains current then continue
      seen := seen.insert current
      let some info := env.find? current | continue
      let value := match info with
        | .thmInfo theorem_ => some theorem_.value
        | .defnInfo definition => some definition.value
        | _ => none
      for e in info.type :: value.toList do
        discard <| liftCoreM <| Core.transform e (pre := fun e => do
          if let .proj name index _ := e then
            if name == structureName then
              if let some field := fields[index]? then found.modify (·.insert field)
          return .continue)
        for constant in e.getUsedConstants do
          if claim.getPrefix.isPrefixOf constant && !seen.contains constant then
            stack := constant :: stack
    let used := (← found.get).toList.map toString |>.mergeSort (· < ·)
    logInfo m!"STATCLAIM_PREMISES {label} {{short}}: {{String.intercalate "," used}}"
"""


def collector(label: str, claims: list[str]) -> str:
    """The Lean command that prints the premises each claim's proof uses."""
    if not claims:
        return ""
    pairs = ", ".join(f'("{claim}", ``{lean(claim)})' for claim in claims)
    return COLLECTOR.format(label=label, pairs=pairs)
