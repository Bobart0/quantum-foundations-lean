import QuantumFoundations.Complexity.Defs

/-!
# C9a — Explicit repetition-model branch states

Configurations are functions `Fin R → Fin 2`.  The explicit equivalence
`finFunctionFinEquiv.symm` identifies their Euclidean basis with the standard
basis of `H (2 ^ R)`.  The coherent repetition state is deliberately left
unnormalized; each of its two branch vectors has norm one.
-/

namespace QuantumFoundations.Complexity.RepetitionModel

open scoped InnerProductSpace Classical

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- The explicit binary expansion equivalence between the standard Hilbert
index and an `R`-bit site configuration. -/
def configurationEquiv (R : ℕ) : Fin (2 ^ R) ≃ (Fin R → Fin 2) :=
  finFunctionFinEquiv.symm

/-- The corresponding coordinate-reindexing linear isometry. -/
def sitesEquivR (R : ℕ) : H (2 ^ R) ≃ₗᵢ[ℂ] Sites R 2 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (configurationEquiv R)

/-- Constant-zero computational configuration. -/
def zeroConfiguration (R : ℕ) : Fin R → Fin 2 := fun _ => 0

/-- Constant-one computational configuration. -/
def oneConfiguration (R : ℕ) : Fin R → Fin 2 := fun _ => 1

/-- All-zero computational basis vector on the site representation. -/
def sitesZero (R : ℕ) : Sites R 2 :=
  EuclideanSpace.single (zeroConfiguration R) 1

/-- All-one computational basis vector on the site representation. -/
def sitesOne (R : ℕ) : Sites R 2 :=
  EuclideanSpace.single (oneConfiguration R) 1

/-- All-zero branch transported to `H (2 ^ R)`. -/
def zeroBranch (R : ℕ) : H (2 ^ R) :=
  (sitesEquivR R).symm (sitesZero R)

/-- All-one branch transported to `H (2 ^ R)`. -/
def oneBranch (R : ℕ) : H (2 ^ R) :=
  (sitesEquivR R).symm (sitesOne R)

/-- Generic computational-basis vector for an arbitrary site configuration,
transported to `H (2 ^ R)`.  `zeroBranch`/`oneBranch` are the special cases at
the constant-zero and constant-one configurations (see
`zeroBranch_eq_configurationBranch`/`oneBranch_eq_configurationBranch`). -/
def configurationBranch (R : ℕ) (f : Fin R → Fin 2) : H (2 ^ R) :=
  (sitesEquivR R).symm (EuclideanSpace.single f 1)

@[simp] theorem sitesEquivR_configurationBranch (R : ℕ) (f : Fin R → Fin 2) :
    sitesEquivR R (configurationBranch R f) = EuclideanSpace.single f 1 := by
  simp [configurationBranch]

theorem zeroBranch_eq_configurationBranch (R : ℕ) :
    zeroBranch R = configurationBranch R (zeroConfiguration R) := rfl

theorem oneBranch_eq_configurationBranch (R : ℕ) :
    oneBranch R = configurationBranch R (oneConfiguration R) := rfl

theorem configurationBranch_norm (R : ℕ) (f : Fin R → Fin 2) :
    ‖configurationBranch R f‖ = 1 := by
  simp [configurationBranch]

theorem configurationBranch_ne_zero (R : ℕ) (f : Fin R → Fin 2) :
    configurationBranch R f ≠ 0 :=
  ne_zero_of_norm_ne_zero (by rw [configurationBranch_norm]; norm_num)

/-- Distinct configurations give orthogonal basis vectors: the single generic
fact underlying every pairwise orthogonality statement between explicit
computational basis states. -/
theorem configurationBranch_inner_eq_zero_of_ne {R : ℕ} {f g : Fin R → Fin 2}
    (hfg : f ≠ g) :
    ⟪configurationBranch R f, configurationBranch R g⟫_ℂ = 0 := by
  simp [configurationBranch, EuclideanSpace.inner_single_left, hfg]

/-- Unnormalized coherent repetition/GHZ state `|0…0⟩ + |1…1⟩`. -/
def repetitionState (R : ℕ) : H (2 ^ R) :=
  zeroBranch R + oneBranch R

@[simp] theorem sitesEquivR_zeroBranch (R : ℕ) :
    sitesEquivR R (zeroBranch R) = sitesZero R := by
  simp [zeroBranch]

@[simp] theorem sitesEquivR_oneBranch (R : ℕ) :
    sitesEquivR R (oneBranch R) = sitesOne R := by
  simp [oneBranch]

theorem zeroBranch_norm (R : ℕ) : ‖zeroBranch R‖ = 1 := by
  simp [zeroBranch, sitesZero]

theorem oneBranch_norm (R : ℕ) : ‖oneBranch R‖ = 1 := by
  simp [oneBranch, sitesOne]

theorem zeroBranch_ne_zero (R : ℕ) : zeroBranch R ≠ 0 :=
  ne_zero_of_norm_ne_zero (by rw [zeroBranch_norm]; norm_num)

theorem oneBranch_ne_zero (R : ℕ) : oneBranch R ≠ 0 :=
  ne_zero_of_norm_ne_zero (by rw [oneBranch_norm]; norm_num)

private theorem zeroConfiguration_ne_oneConfiguration (R : ℕ) [NeZero R] :
    zeroConfiguration R ≠ oneConfiguration R := by
  intro h
  have hpoint := congrFun h (0 : Fin R)
  change (0 : Fin 2) = 1 at hpoint
  exact Fin.zero_ne_one hpoint

theorem zeroBranch_inner_oneBranch (R : ℕ) [NeZero R] :
    ⟪zeroBranch R, oneBranch R⟫_ℂ = 0 := by
  simp [zeroBranch, oneBranch, sitesZero, sitesOne,
    EuclideanSpace.inner_single_left, zeroConfiguration_ne_oneConfiguration R]

theorem zeroBranch_ne_oneBranch (R : ℕ) [NeZero R] :
    zeroBranch R ≠ oneBranch R := by
  intro h
  have hinner := zeroBranch_inner_oneBranch R
  rw [← h, inner_self_eq_norm_sq_to_K, zeroBranch_norm] at hinner
  norm_num at hinner

theorem repetitionState_ne_zero (R : ℕ) [NeZero R] :
    repetitionState R ≠ 0 := by
  intro h
  have hinner := congrArg (fun x => ⟪zeroBranch R, x⟫_ℂ) h
  simp only [repetitionState, inner_add_right, zeroBranch_inner_oneBranch,
    inner_zero_right, add_zero] at hinner
  rw [inner_self_eq_norm_sq_to_K, zeroBranch_norm] at hinner
  norm_num at hinner

end

end QuantumFoundations.Complexity.RepetitionModel
