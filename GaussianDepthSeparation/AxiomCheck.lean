/-
Build-time verification of the logical dependencies of GaussianDepthSeparation declarations.
This module contains checking code only; it introduces no mathematical axioms.
-/
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace GaussianDepthSeparationVerification

/-- Classical foundations accepted by the development. In particular, neither
`sorryAx` nor native-evaluation axioms are permitted. -/
def allowedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

/-- Fail elaboration if a declaration is missing or depends transitively on an
axiom outside the explicit allowlist. -/
def checkAxioms (names : Array Name) : CommandElabM Unit := do
  for name in names do
    unless (← getEnv).contains name do
      throwError "axiom audit: unknown declaration {name}"
    let unexpected := (← collectAxioms name).filter (!allowedAxioms.contains ·)
    unless unexpected.isEmpty do
      throwError "axiom audit: {name} depends on forbidden axioms {unexpected.toList}"

/-- Check all declarations from imported GaussianDepthSeparation modules and the current module,
including private helpers and declarations outside the GaussianDepthSeparation namespace.
Module ownership keeps standalone negative tests outside the proof-library audit. -/
def checkGaussianDepthSeparation : CommandElabM Unit := do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      let mod := env.header.moduleNames[idx]!
      if (`GaussianDepthSeparation).isPrefixOf mod && mod != `GaussianDepthSeparation.AxiomCheck then names.push name else names
    | none => names.push name
  if names.isEmpty then
    throwError "axiom audit: no imported GaussianDepthSeparation declarations found"
  checkAxioms names
  logInfo m!"GaussianDepthSeparation axiom audit passed ({names.size} declarations; allowed: {allowedAxioms.toList})"

end GaussianDepthSeparationVerification
