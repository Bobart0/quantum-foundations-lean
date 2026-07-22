import QuantumFoundations.Complexity.OperatorNorm.NoisyRepetition
import QuantumFoundations.Complexity.Models.MeasurementGeneration.ConcreteGeneration

/-!
# C12g — Dynamically generated branch corollaries

Connects C11's unitary branch generation to C12's operator-norm readout
robustness. The full generation circuit `noisyMeasurementCircuit p R` turns
the (blank-record) source superposition `noisySourceInputState q R` into
exactly `q.amp0 • noisyZeroBranch p R + q.amp1 • noisyOneBranch p R`
(`noisyMeasurement_generates_branching`, unchanged from C11); the *generated*
branch pair `noisyZeroBranch p R`/`noisyOneBranch p R` then carries the
robust operator-norm proxy gap of C12f. The gap concerns this normalized
branch pair itself, not the `q`-scaled global superposition (which need not
be a unit vector unless `q.amp0`, `q.amp1` are chosen so). No nontriviality
hypothesis on `q.amp0`/`q.amp1` is needed for either conclusion below: the
generation equality holds for every `q`, and the branch-pair gap does not
depend on `q` at all.
-/

namespace QuantumFoundations.Complexity.OperatorNorm

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel
open QuantumFoundations.Complexity.MeasurementGeneration

noncomputable section

/-- The full unitary generation circuit reaches exactly the `q`-weighted
noisy branch decomposition, and the generated branch pair itself carries a
robust operator-norm proxy gap. -/
theorem generated_branches_have_opNorm_robust_gap
    (p : NoiseProfile) (hp : p.IsRobust) (q : SourceAmplitudeProfile)
    (R : ℕ) [NeZero R]
    (D : Circuit (R + 1) 2) (ε : ℝ)
    (hOp : ApproximatesRecordPhaseFlipOp
      (sitesEquivR (R + 1)) D (noisyRecords R 0) 1 ε)
    (hreadout : 4 * ‖p.leak‖ + 2 * ε ≤ 1)
    (g : ℕ) (hgap : Circuit.length D + g ≤ ceilHalf R) :
    Circuit.evalOnH (noisyMeasurementCircuit p R) (sitesEquivR (R + 1))
        (noisySourceInputState q R) =
      q.amp0 • noisyZeroBranch p R + q.amp1 • noisyOneBranch p R
    ∧
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ) g :=
  ⟨noisyMeasurement_generates_branching q.amp0 q.amp1 p R,
    noisy_repetition_opNorm_readout_has_gap p hp R D ε hOp hreadout g hgap⟩

/-- The evolved global generated state, and the persistent gap of the
evolved branch pair, after a further finite `2`-local circuit `E`. The
budget `Circuit.length D + 4 * Circuit.length E + g` measures evolution
*after* generation: the generation circuit's own length is not added again,
since `noisyMeasurementCircuit p R` is never evolved or conjugated — only
the readout circuit `D`'s operator-norm certificate is transported by the
existing C7/C8 persistence machinery. -/
theorem generated_branches_opNorm_gap_persists
    (p : NoiseProfile) (hp : p.IsRobust) (q : SourceAmplitudeProfile)
    (R : ℕ) [NeZero R]
    (D : Circuit (R + 1) 2) (ε : ℝ)
    (hOp : ApproximatesRecordPhaseFlipOp
      (sitesEquivR (R + 1)) D (noisyRecords R 0) 1 ε)
    (hreadout : 4 * ‖p.leak‖ + 2 * ε ≤ 1)
    (E : Circuit (R + 1) 2) (g : ℕ)
    (hbudget : Circuit.length D + 4 * Circuit.length E + g ≤ ceilHalf R) :
    Circuit.evalOnH E (sitesEquivR (R + 1))
        (Circuit.evalOnH (noisyMeasurementCircuit p R) (sitesEquivR (R + 1))
          (noisySourceInputState q R)) =
      Circuit.evalOnH E (sitesEquivR (R + 1))
        (q.amp0 • noisyZeroBranch p R + q.amp1 • noisyOneBranch p R)
    ∧
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (Circuit.evalOnH E (sitesEquivR (R + 1)) (noisyZeroBranch p R))
      (Circuit.evalOnH E (sitesEquivR (R + 1)) (noisyOneBranch p R))
      (1 / 2 : ℝ) g :=
  ⟨congrArg (Circuit.evalOnH E (sitesEquivR (R + 1)))
      (noisyMeasurement_generates_branching q.amp0 q.amp1 p R),
    noisy_repetition_opNorm_gap_persists p hp R D ε hOp hreadout E g hbudget⟩

#print axioms generated_branches_have_opNorm_robust_gap
#print axioms generated_branches_opNorm_gap_persists

end

end QuantumFoundations.Complexity.OperatorNorm
