import QuantumFoundations.Complexity.Models.NoisyRepetition.Profiles
import QuantumFoundations.Complexity.Models.Repetition.States

/-!
# C10b — Four basis configurations and noisy branch states

The site system has `R + 1` sites: site `0` is a distinguished source qubit,
and sites `r + 1` (`r : Fin R`) are the `R` record qubits.  Four
computational-basis configurations matter: the source bit crossed with the
constant record bit.  A `NoiseProfile` mixes the two same-source-bit
configurations, `keep` weighting the "correctly aligned" tail and `leak`
weighting the flipped tail.  Because the two noisy branches keep distinct
source-qubit values, they stay exactly orthogonal even though `leak ≠ 0`.
-/

namespace QuantumFoundations.Complexity.NoisyRepetitionModel

open scoped InnerProductSpace Classical

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity.RepetitionModel

noncomputable section

/-! ## C10b.1 — Source and record sites -/

/-- The distinguished source qubit: site `0` of `R + 1`. -/
def sourceSite (R : ℕ) : Fin (R + 1) := 0

/-- Record site `r : Fin R` embedded as site `r + 1` of `R + 1`. -/
def recordSite {R : ℕ} (r : Fin R) : Fin (R + 1) := Fin.succ r

theorem recordSite_ne_sourceSite {R : ℕ} (r : Fin R) :
    recordSite r ≠ sourceSite R :=
  Fin.succ_ne_zero r

theorem recordSite_injective {R : ℕ} : Function.Injective (recordSite (R := R)) :=
  Fin.succ_injective R

/-! ## C10b.2 — Basis configurations -/

/-- Source `0`, all records `0`. -/
def config00 (R : ℕ) : Fin (R + 1) → Fin 2 := fun _ => 0

/-- Source `0`, all records `1`. -/
def config01 (R : ℕ) : Fin (R + 1) → Fin 2 := Fin.cases 0 (fun _ => 1)

/-- Source `1`, all records `0`. -/
def config10 (R : ℕ) : Fin (R + 1) → Fin 2 := Fin.cases 1 (fun _ => 0)

/-- Source `1`, all records `1`. -/
def config11 (R : ℕ) : Fin (R + 1) → Fin 2 := fun _ => 1

@[simp] theorem config00_source (R : ℕ) : config00 R (sourceSite R) = 0 := rfl
@[simp] theorem config01_source (R : ℕ) : config01 R (sourceSite R) = 0 := rfl
@[simp] theorem config10_source (R : ℕ) : config10 R (sourceSite R) = 1 := rfl
@[simp] theorem config11_source (R : ℕ) : config11 R (sourceSite R) = 1 := rfl

@[simp] theorem config00_record (R : ℕ) (r : Fin R) : config00 R (recordSite r) = 0 := rfl
@[simp] theorem config01_record (R : ℕ) (r : Fin R) : config01 R (recordSite r) = 1 :=
  Fin.cases_succ r
@[simp] theorem config10_record (R : ℕ) (r : Fin R) : config10 R (recordSite r) = 0 :=
  Fin.cases_succ r
@[simp] theorem config11_record (R : ℕ) (r : Fin R) : config11 R (recordSite r) = 1 := rfl

theorem config00_ne_config10 (R : ℕ) : config00 R ≠ config10 R := by
  intro h
  have := congrFun h (sourceSite R)
  simp at this

theorem config00_ne_config11 (R : ℕ) : config00 R ≠ config11 R := by
  intro h
  have := congrFun h (sourceSite R)
  simp at this

theorem config01_ne_config10 (R : ℕ) : config01 R ≠ config10 R := by
  intro h
  have := congrFun h (sourceSite R)
  simp at this

theorem config01_ne_config11 (R : ℕ) : config01 R ≠ config11 R := by
  intro h
  have := congrFun h (sourceSite R)
  simp at this

theorem config00_ne_config01 (R : ℕ) [NeZero R] : config00 R ≠ config01 R := by
  intro h
  have := congrFun h (recordSite (⟨0, NeZero.pos R⟩ : Fin R))
  simp at this

theorem config10_ne_config11 (R : ℕ) [NeZero R] : config10 R ≠ config11 R := by
  intro h
  have := congrFun h (recordSite (⟨0, NeZero.pos R⟩ : Fin R))
  simp at this

/-! ## C10b.3 — Basis states -/

/-- Basis vector for `config00`, transported to `H (2 ^ (R + 1))`. -/
def basis00 (R : ℕ) : H (2 ^ (R + 1)) := configurationBranch (R + 1) (config00 R)

/-- Basis vector for `config01`, transported to `H (2 ^ (R + 1))`. -/
def basis01 (R : ℕ) : H (2 ^ (R + 1)) := configurationBranch (R + 1) (config01 R)

/-- Basis vector for `config10`, transported to `H (2 ^ (R + 1))`. -/
def basis10 (R : ℕ) : H (2 ^ (R + 1)) := configurationBranch (R + 1) (config10 R)

/-- Basis vector for `config11`, transported to `H (2 ^ (R + 1))`. -/
def basis11 (R : ℕ) : H (2 ^ (R + 1)) := configurationBranch (R + 1) (config11 R)

theorem basis00_norm (R : ℕ) : ‖basis00 R‖ = 1 := configurationBranch_norm (R + 1) (config00 R)
theorem basis01_norm (R : ℕ) : ‖basis01 R‖ = 1 := configurationBranch_norm (R + 1) (config01 R)
theorem basis10_norm (R : ℕ) : ‖basis10 R‖ = 1 := configurationBranch_norm (R + 1) (config10 R)
theorem basis11_norm (R : ℕ) : ‖basis11 R‖ = 1 := configurationBranch_norm (R + 1) (config11 R)

theorem basis00_ne_zero (R : ℕ) : basis00 R ≠ 0 := configurationBranch_ne_zero (R + 1) (config00 R)
theorem basis01_ne_zero (R : ℕ) : basis01 R ≠ 0 := configurationBranch_ne_zero (R + 1) (config01 R)
theorem basis10_ne_zero (R : ℕ) : basis10 R ≠ 0 := configurationBranch_ne_zero (R + 1) (config10 R)
theorem basis11_ne_zero (R : ℕ) : basis11 R ≠ 0 := configurationBranch_ne_zero (R + 1) (config11 R)

theorem basis00_inner_basis10 (R : ℕ) : ⟪basis00 R, basis10 R⟫_ℂ = 0 :=
  configurationBranch_inner_eq_zero_of_ne (config00_ne_config10 R)

theorem basis00_inner_basis11 (R : ℕ) : ⟪basis00 R, basis11 R⟫_ℂ = 0 :=
  configurationBranch_inner_eq_zero_of_ne (config00_ne_config11 R)

theorem basis01_inner_basis10 (R : ℕ) : ⟪basis01 R, basis10 R⟫_ℂ = 0 :=
  configurationBranch_inner_eq_zero_of_ne (config01_ne_config10 R)

theorem basis01_inner_basis11 (R : ℕ) : ⟪basis01 R, basis11 R⟫_ℂ = 0 :=
  configurationBranch_inner_eq_zero_of_ne (config01_ne_config11 R)

theorem basis00_inner_basis01 (R : ℕ) [NeZero R] : ⟪basis00 R, basis01 R⟫_ℂ = 0 :=
  configurationBranch_inner_eq_zero_of_ne (config00_ne_config01 R)

theorem basis10_inner_basis11 (R : ℕ) [NeZero R] : ⟪basis10 R, basis11 R⟫_ℂ = 0 :=
  configurationBranch_inner_eq_zero_of_ne (config10_ne_config11 R)

/-! ## C10b.4 — Noisy branches -/

/-- The noisy zero branch: `keep • |source 0, records 0⟩ + leak • |source 0,
records 1⟩`.  The source qubit stays `0` on both terms. -/
def noisyZeroBranch (p : NoiseProfile) (R : ℕ) : H (2 ^ (R + 1)) :=
  p.keep • basis00 R + p.leak • basis01 R

/-- The noisy one branch: `leak • |source 1, records 0⟩ + keep • |source 1,
records 1⟩`.  The source qubit stays `1` on both terms, so it remains exactly
orthogonal to `noisyZeroBranch` regardless of `leak`. -/
def noisyOneBranch (p : NoiseProfile) (R : ℕ) : H (2 ^ (R + 1)) :=
  p.leak • basis10 R + p.keep • basis11 R

/-- Pythagorean norm identity for a `keep`/`leak` combination of two
orthogonal unit vectors: the generic fact underlying both branch norms.
Not `private`: also reused directly by the `MeasurementGeneration` block
(C11) for the source-amplitude combinations. -/
theorem norm_mul_self_keep_leak_combo {n : ℕ} (x y : H n) (a b : ℂ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ⟪x, y⟫_ℂ = 0) :
    ‖a • x + b • y‖ * ‖a • x + b • y‖ = ‖a‖ * ‖a‖ + ‖b‖ * ‖b‖ := by
  have hxy' : ⟪a • x, b • y⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, hxy]
    ring
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hxy',
    norm_smul, norm_smul, hx, hy, mul_one, mul_one]

/-- Not `private`: also reused directly by the `MeasurementGeneration`
block (C11). -/
theorem norm_eq_one_of_mul_self_eq_one {n : ℕ} {x : H n}
    (h : ‖x‖ * ‖x‖ = 1) : ‖x‖ = 1 := by
  have hx2 : (‖x‖ - 1) * (‖x‖ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hx2 with h1 | h1
  · linarith
  · linarith [norm_nonneg x]

theorem noisyZeroBranch_norm (p : NoiseProfile) (R : ℕ) [NeZero R] :
    ‖noisyZeroBranch p R‖ = 1 := by
  apply norm_eq_one_of_mul_self_eq_one
  rw [noisyZeroBranch, norm_mul_self_keep_leak_combo (basis00 R) (basis01 R) p.keep p.leak
    (basis00_norm R) (basis01_norm R) (basis00_inner_basis01 R)]
  nlinarith [p.norm_sq]

theorem noisyOneBranch_norm (p : NoiseProfile) (R : ℕ) [NeZero R] :
    ‖noisyOneBranch p R‖ = 1 := by
  apply norm_eq_one_of_mul_self_eq_one
  rw [noisyOneBranch, norm_mul_self_keep_leak_combo (basis10 R) (basis11 R) p.leak p.keep
    (basis10_norm R) (basis11_norm R) (basis10_inner_basis11 R)]
  nlinarith [p.norm_sq]

theorem noisyZeroBranch_ne_zero (p : NoiseProfile) (R : ℕ) [NeZero R] :
    noisyZeroBranch p R ≠ 0 :=
  ne_zero_of_norm_ne_zero (by rw [noisyZeroBranch_norm]; norm_num)

theorem noisyOneBranch_ne_zero (p : NoiseProfile) (R : ℕ) [NeZero R] :
    noisyOneBranch p R ≠ 0 :=
  ne_zero_of_norm_ne_zero (by rw [noisyOneBranch_norm]; norm_num)

theorem noisyBranches_inner (p : NoiseProfile) (R : ℕ) :
    ⟪noisyZeroBranch p R, noisyOneBranch p R⟫_ℂ = 0 := by
  simp only [noisyZeroBranch, noisyOneBranch, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right,
    basis00_inner_basis10 R, basis00_inner_basis11 R,
    basis01_inner_basis10 R, basis01_inner_basis11 R]
  ring

theorem noisyBranches_orthogonal (p : NoiseProfile) (R : ℕ) :
    ⟪noisyOneBranch p R, noisyZeroBranch p R⟫_ℂ = 0 := by
  rw [← inner_conj_symm, noisyBranches_inner]
  simp

/-- The unnormalized noisy coherent state.  No `IsRecordedOn` claim is made:
its records are approximate by construction. -/
def noisyRepetitionState (p : NoiseProfile) (R : ℕ) : H (2 ^ (R + 1)) :=
  noisyZeroBranch p R + noisyOneBranch p R

#print axioms noisyZeroBranch_norm
#print axioms noisyOneBranch_norm

end

end QuantumFoundations.Complexity.NoisyRepetitionModel
