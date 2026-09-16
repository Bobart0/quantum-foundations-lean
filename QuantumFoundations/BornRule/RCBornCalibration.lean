import QuantumFoundations.BornRule.RefinementClosure
import QuantumFoundations.BornRule.Assembly

/-!
# Born calibration from finite refinement consistency

This file exposes the short composite theorem used by the compact note.  The
weight assignment is pre-probabilistic: normalization and positivity remain
explicit assumptions rather than fields of the type.
-/

namespace QuantumFoundations.BornRule

open scoped Classical InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/-- Finite refinement consistency, normalization, positivity, and projective
null support relative to a unit vector force the pure-state Born weights in
dimension at least three. -/
theorem rcBornCalibration_projector
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hn3 : 3 ≤ n)
    (hRC : AxRC Est)
    (hNorm : AxNorm Est)
    (hPos : AxPos Est)
    {v : H n} (hv : ‖v‖ = 1)
    (hNul : AxNul Est v)
    (D : Perspective n) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    Est D c = ‖projL c v‖ ^ 2 := by
  exact grainCoherenceTheorem_projector Est hn3
    (axRC_norm_implies_axGrain Est hRC hNorm) hNorm hPos hv hNul D hc

end

end QuantumFoundations.BornRule
