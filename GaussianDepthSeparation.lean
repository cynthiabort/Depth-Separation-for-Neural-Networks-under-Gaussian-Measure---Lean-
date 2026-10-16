/-
Root module for the Lean verification of `main.tex`,
"Depth Separation for Neural Networks under Gaussian Measure".

See `VERIFICATION.md` for the statement map and proof-fidelity boundary.
-/
import GaussianDepthSeparation.Spectral
import GaussianDepthSeparation.Target
import GaussianDepthSeparation.Hermite
import GaussianDepthSeparation.Chaos
import GaussianDepthSeparation.RadialAverage
import GaussianDepthSeparation.Radialization
import GaussianDepthSeparation.Moments
import GaussianDepthSeparation.GaussianTail
import GaussianDepthSeparation.Correlation
import GaussianDepthSeparation.LowerBound
import GaussianDepthSeparation.EnergyBound
import GaussianDepthSeparation.ReLU
import GaussianDepthSeparation.DepthSeparation
import GaussianDepthSeparation.CenteredReLU
import GaussianDepthSeparation.GlobalUpper
import GaussianDepthSeparation.MultivariateTotality
import GaussianDepthSeparation.DepthTwo
import GaussianDepthSeparation.DepthComparison
import GaussianDepthSeparation.DepthSeparationTheorem
import GaussianDepthSeparation.PolynomialCriterion
import GaussianDepthSeparation.AxiomCheck

-- This must remain after the mathematical imports: a forbidden dependency
-- makes both `lake build` and `lake build GaussianDepthSeparation` fail.
run_cmd GaussianDepthSeparationVerification.checkGaussianDepthSeparation
