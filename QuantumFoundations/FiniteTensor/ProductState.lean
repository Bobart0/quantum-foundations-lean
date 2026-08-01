import QuantumFoundations.FiniteTensor.Reindex
namespace QuantumFoundations.FiniteTensor
open QuantumFoundations
open Gleason
open scoped InnerProductSpace
noncomputable section

def productStateCoordinates {n a : ℕ} (ψ : H n) (η : H a) : BipartiteSpace n a :=
  WithLp.toLp 2 (fun p : Fin a × Fin n => η p.1 * ψ p.2)

@[simp] theorem productStateCoordinates_apply {n a : ℕ} (ψ : H n) (η : H a)
    (j : Fin a) (i : Fin n) : productStateCoordinates ψ η (j, i) = η j * ψ i := by
  rfl

theorem productStateCoordinates_zero_left {n a : ℕ} (η : H a) : productStateCoordinates (0 : H n) η = 0 := by
  ext p
  simp [productStateCoordinates]

theorem productStateCoordinates_zero_right {n a : ℕ} (ψ : H n) : productStateCoordinates ψ (0 : H a) = 0 := by
  ext p
  simp [productStateCoordinates]

theorem productStateCoordinates_add_left {n a : ℕ} (ψ ψ' : H n) (η : H a) :
    productStateCoordinates (ψ + ψ') η = productStateCoordinates ψ η + productStateCoordinates ψ' η := by
  ext p
  simp [productStateCoordinates, mul_add]

theorem productStateCoordinates_add_right {n a : ℕ} (ψ : H n) (η η' : H a) :
    productStateCoordinates ψ (η + η') = productStateCoordinates ψ η + productStateCoordinates ψ η' := by
  ext p
  simp [productStateCoordinates, add_mul]

theorem productStateCoordinates_smul_left {n a : ℕ} (c : ℂ) (ψ : H n) (η : H a) :
    productStateCoordinates (c • ψ) η = c • productStateCoordinates ψ η := by
  ext p
  simp [productStateCoordinates, mul_assoc, mul_comm]

theorem productStateCoordinates_smul_right {n a : ℕ} (c : ℂ) (ψ : H n) (η : H a) :
    productStateCoordinates ψ (c • η) = c • productStateCoordinates ψ η := by
  ext p
  simp [productStateCoordinates, mul_assoc]

theorem inner_productStateCoordinates {n a : ℕ} (ψ ψ' : H n) (η η' : H a) :
    ⟪productStateCoordinates ψ η, productStateCoordinates ψ' η'⟫_ℂ = ⟪ψ, ψ'⟫_ℂ * ⟪η, η'⟫_ℂ := by
  rw [PiLp.inner_apply]
  simp only [productStateCoordinates, WithLp.ofLp_toLp, RCLike.inner_apply, starRingEnd_apply, StarMul.star_mul]
  rw [Fintype.sum_prod_type]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  change (∑ j : Fin a, ∑ i : Fin n, η' j * ψ' i * (star (ψ i) * star (η j))) = _
  have hbody : ∀ (j : Fin a) (i : Fin n),
      η' j * ψ' i * (star (ψ i) * star (η j)) = (η' j * star (η j)) * (ψ' i * star (ψ i)) := by
    intro j i
    ring
  simp_rw [hbody]
  simp_rw [← Finset.mul_sum (s := Finset.univ)]
  rw [← Finset.sum_mul (s := Finset.univ)]
  simp only [starRingEnd_apply]
  ring

theorem norm_productStateCoordinates {n a : ℕ} (ψ : H n) (η : H a) :
    ‖productStateCoordinates ψ η‖ = ‖ψ‖ * ‖η‖ := by
  have hsq : ‖productStateCoordinates ψ η‖ ^ 2 = (‖ψ‖ * ‖η‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [productStateCoordinates, WithLp.ofLp_toLp, norm_mul, mul_pow]
    rw [Fintype.sum_prod_type]
    change (∑ y : Fin a, ∑ x : Fin n, ‖η y‖ ^ 2 * ‖ψ x‖ ^ 2) = _
    simp_rw [← Finset.mul_sum (s := Finset.univ)]
    rw [← Finset.sum_mul (s := Finset.univ)]
    rw [← PiLp.norm_sq_eq_of_L2 (fun _ : Fin a => ℂ) η]
    rw [← PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℂ) ψ]
    ring
  have hprod : 0 ≤ ‖ψ‖ * ‖η‖ := mul_nonneg (norm_nonneg ψ) (norm_nonneg η)
  nlinarith [norm_nonneg (productStateCoordinates ψ η)]

theorem productStateCoordinates_norm_one {n a : ℕ} {ψ : H n} {η : H a}
    (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) : ‖productStateCoordinates ψ η‖ = 1 := by
  rw [norm_productStateCoordinates, hψ, hη, one_mul]

namespace TensorDecomposition
variable {n a : ℕ} (D : TensorDecomposition n a)

def productState (ψ : H n) (η : H a) : H (n * a) := D.toBipartite.symm (productStateCoordinates ψ η)

theorem toBipartite_productState (ψ : H n) (η : H a) :
    D.toBipartite (D.productState ψ η) = productStateCoordinates ψ η := by
  simp [productState]

theorem norm_productState (ψ : H n) (η : H a) : ‖D.productState ψ η‖ = ‖ψ‖ * ‖η‖ := by
  rw [productState, LinearIsometryEquiv.norm_map, norm_productStateCoordinates]

theorem productState_norm_one {ψ : H n} {η : H a} (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) :
    ‖D.productState ψ η‖ = 1 := by
  rw [norm_productState, hψ, hη, one_mul]

end TensorDecomposition
end
end QuantumFoundations.FiniteTensor
