/-
Regression tests for the axiom gate. Deliberately untrusted fixtures live in
this standalone test module and are never imported by the mathematical library.
Run with `lake build GaussianDepthSeparationAuditTests` (also included in the default build).
-/
import GaussianDepthSeparation.AxiomCheck
import Lean.Elab.GuardMsgs

/-- error: axiom audit: no imported GaussianDepthSeparation declarations found -/
#guard_msgs in
run_cmd GaussianDepthSeparationVerification.checkGaussianDepthSeparation

namespace AxiomAuditTests

theorem allowed (p : Prop) : p ∨ ¬p := Classical.em p

run_cmd GaussianDepthSeparationVerification.checkAxioms #[`AxiomAuditTests.allowed]

private axiom hiddenForbidden : True

/-- error: axiom audit: _private.GaussianDepthSeparationAuditTests.0.AxiomAuditTests.hiddenForbidden depends on forbidden axioms [_private.GaussianDepthSeparationAuditTests.0.AxiomAuditTests.hiddenForbidden] -/
#guard_msgs in
run_cmd GaussianDepthSeparationVerification.checkGaussianDepthSeparation

axiom forbidden : True
theorem indirect : True := forbidden

/-- error: axiom audit: AxiomAuditTests.indirect depends on forbidden axioms [AxiomAuditTests.forbidden] -/
#guard_msgs in
run_cmd GaussianDepthSeparationVerification.checkAxioms #[`AxiomAuditTests.indirect]

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem admitted : True := by sorry

/-- error: axiom audit: AxiomAuditTests.admitted depends on forbidden axioms [sorryAx] -/
#guard_msgs in
run_cmd GaussianDepthSeparationVerification.checkAxioms #[`AxiomAuditTests.admitted]

/-- error: axiom audit: unknown declaration AxiomAuditTests.missing -/
#guard_msgs in
run_cmd GaussianDepthSeparationVerification.checkAxioms #[`AxiomAuditTests.missing]

end AxiomAuditTests
