import Solution
import Lean

/-!
# Axiom audit (part of the default build)

The build fails unless
1. `oeis_60957_conjecture_0.disproof`, `Ang.disproof` and `Ang.counterexample` depend only on the
   axioms `propext`, `Classical.choice` and `Quot.sound` (in particular not on `sorryAx`), and
2. no declaration of `AngCounterexample.*` or `Solution` uses `sorry` directly.
-/

open Lean Elab Command

elab "#ang_audit" : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for h in [``oeis_60957_conjecture_0.disproof, ``Ang.disproof, ``Ang.counterexample] do
    let axs := (← liftCoreM <| Lean.collectAxioms h).toList
    logInfo m!"AUDIT axioms {h}: {axs}"
    for a in axs do
      unless std.contains a do
        logError m!"AUDIT FAIL {h}: forbidden axiom {a}"
  let mods := env.header.moduleNames
  let direct := env.constants.map₁.fold (init := (#[] : Array Name)) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := mods[idx.toNat]!
      if (m.getRoot == `AngCounterexample || m == `Solution) &&
          ci.getUsedConstantsAsSet.contains ``sorryAx then
        acc.push n
      else acc
    | none => acc
  logInfo m!"AUDIT declarations using sorry directly: {direct.toList}"
  unless direct.isEmpty do
    logError m!"AUDIT FAIL: declarations using sorry: {direct.toList}"

#ang_audit


/-! The original v1 audit above is retained unchanged. The v2 audit adds
all new public heads and the principal construction theorems. -/
elab "#ang_large_audit" : command => do
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for h in [``large_prime_counterexamples, ``large_prime_interval_conjecture_false,
      ``AngLarge.large_prime_counterexamples, ``AngLarge.large_prime_interval_conjecture_false,
      ``AngLarge.saturated_residual_gap, ``AngLarge.large_realization] do
    let axs := (← liftCoreM <| Lean.collectAxioms h).toList
    logInfo m!"AUDIT axioms {h}: {axs}"
    for a in axs do
      unless std.contains a do
        logError m!"AUDIT FAIL {h}: forbidden axiom {a}"
  let env ← getEnv
  let mods := env.header.moduleNames
  let localDecls := env.constants.map₁.fold (init := (#[] : Array Name)) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := mods[idx.toNat]!
      if m.getRoot == `AngCounterexample || m == `Solution then acc.push n else acc
    | none => acc
  for n in localDecls do
    for a in (← liftCoreM <| Lean.collectAxioms n).toList do
      unless std.contains a do
        logError m!"AUDIT FAIL {n}: forbidden axiom {a}"
  logInfo m!"AUDIT all development declarations checked: {localDecls.size}"
  logInfo m!"AUDIT placeholders (0): []"

#ang_large_audit
