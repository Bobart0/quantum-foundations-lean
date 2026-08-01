import QuantumFoundations.Naimark.BinaryImpl.Residual

namespace QuantumFoundations.Naimark.BinaryImpl
open QuantumFoundations Gleason
open scoped InnerProductSpace
noncomputable section

def euclideanSumInl (α β : Type) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ (Sum α β) where
  toFun x := WithLp.toLp 2 (fun j => match j with | Sum.inl a => x a | Sum.inr _ => 0)
  map_add' x y := by rw [← WithLp.toLp_add]; congr 1; funext j; cases j <;> simp
  map_smul' c x := by rw [← WithLp.toLp_smul]; congr 1; funext j; cases j <;> simp

def euclideanSumInr (α β : Type) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ (Sum α β) where
  toFun y := WithLp.toLp 2 (fun j => match j with | Sum.inl _ => 0 | Sum.inr b => y b)
  map_add' x y := by rw [← WithLp.toLp_add]; congr 1; funext j; cases j <;> simp
  map_smul' c x := by rw [← WithLp.toLp_smul]; congr 1; funext j; cases j <;> simp

def euclideanSumFst (α β : Type) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] : EuclideanSpace ℂ (Sum α β) →ₗ[ℂ] EuclideanSpace ℂ α where
  toFun z := WithLp.toLp 2 (fun a => z (Sum.inl a))
  map_add' x y := by rw [← WithLp.toLp_add]; congr 1
  map_smul' c x := by rw [← WithLp.toLp_smul]; congr 1

def euclideanSumSnd (α β : Type) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] : EuclideanSpace ℂ (Sum α β) →ₗ[ℂ] EuclideanSpace ℂ β where
  toFun z := WithLp.toLp 2 (fun b => z (Sum.inr b))
  map_add' x y := by rw [← WithLp.toLp_add]; congr 1
  map_smul' c x := by rw [← WithLp.toLp_smul]; congr 1

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem euclideanSumFst_inl_apply (x : EuclideanSpace ℂ α) :
    euclideanSumFst α β (euclideanSumInl α β x) = x := by
  apply PiLp.ext; intro a; simp [euclideanSumFst, euclideanSumInl]
theorem euclideanSumSnd_inr_apply (y : EuclideanSpace ℂ β) :
    euclideanSumSnd α β (euclideanSumInr α β y) = y := by
  apply PiLp.ext; intro b; simp [euclideanSumSnd, euclideanSumInr]
theorem euclideanSumFst_inr_apply (y : EuclideanSpace ℂ β) :
    euclideanSumFst α β (euclideanSumInr α β y) = 0 := by
  apply PiLp.ext; intro a; simp [euclideanSumFst, euclideanSumInr]
theorem euclideanSumSnd_inl_apply (x : EuclideanSpace ℂ α) :
    euclideanSumSnd α β (euclideanSumInl α β x) = 0 := by
  apply PiLp.ext; intro b; simp [euclideanSumSnd, euclideanSumInl]

theorem euclideanSum_decomposition (z : EuclideanSpace ℂ (Sum α β)) :
    euclideanSumInl α β (euclideanSumFst α β z) + euclideanSumInr α β (euclideanSumSnd α β z) = z := by
  apply PiLp.ext; intro j; cases j with
  | inl a => simp [euclideanSumInl, euclideanSumInr, euclideanSumFst, euclideanSumSnd]
  | inr b => simp [euclideanSumInl, euclideanSumInr, euclideanSumFst, euclideanSumSnd]

theorem euclideanSumFst_comp_inl : euclideanSumFst α β ∘ₗ euclideanSumInl α β = LinearMap.id := by
  apply LinearMap.ext; intro x
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using euclideanSumFst_inl_apply x
theorem euclideanSumSnd_comp_inr : euclideanSumSnd α β ∘ₗ euclideanSumInr α β = LinearMap.id := by
  apply LinearMap.ext; intro y
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using euclideanSumSnd_inr_apply y
theorem euclideanSumFst_comp_inr : euclideanSumFst α β ∘ₗ euclideanSumInr α β = 0 := by
  apply LinearMap.ext; intro y
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using euclideanSumFst_inr_apply y
theorem euclideanSumSnd_comp_inl : euclideanSumSnd α β ∘ₗ euclideanSumInl α β = 0 := by
  apply LinearMap.ext; intro x
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using euclideanSumSnd_inl_apply x
theorem euclideanSum_inl_fst_add_inr_snd :
    euclideanSumInl α β ∘ₗ euclideanSumFst α β + euclideanSumInr α β ∘ₗ euclideanSumSnd α β = LinearMap.id := by
  apply LinearMap.ext; intro z
  change euclideanSumInl α β (euclideanSumFst α β z) + euclideanSumInr α β (euclideanSumSnd α β z) = z
  exact euclideanSum_decomposition z

theorem inner_euclideanSumInl (x : EuclideanSpace ℂ α) (z : EuclideanSpace ℂ (Sum α β)) :
    ⟪euclideanSumInl α β x, z⟫_ℂ = ⟪x, euclideanSumFst α β z⟫_ℂ := by
  show ⟪WithLp.toLp 2 (fun j : Sum α β => match j with | Sum.inl a => x a | Sum.inr _ => 0), z⟫_ℂ = _
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_sum_type]
  simp [euclideanSumFst]
theorem inner_euclideanSumInr (y : EuclideanSpace ℂ β) (z : EuclideanSpace ℂ (Sum α β)) :
    ⟪euclideanSumInr α β y, z⟫_ℂ = ⟪y, euclideanSumSnd α β z⟫_ℂ := by
  show ⟪WithLp.toLp 2 (fun j : Sum α β => match j with | Sum.inl _ => 0 | Sum.inr b => y b), z⟫_ℂ = _
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_sum_type]
  simp [euclideanSumSnd]
theorem adjoint_euclideanSumInl : LinearMap.adjoint (euclideanSumInl α β) = euclideanSumFst α β := by
  symm; rw [LinearMap.eq_adjoint_iff]; intro x y
  rw [← inner_conj_symm (euclideanSumFst α β x) y, ← inner_euclideanSumInl y x, inner_conj_symm]
theorem adjoint_euclideanSumFst : LinearMap.adjoint (euclideanSumFst α β) = euclideanSumInl α β := by
  rw [← adjoint_euclideanSumInl, LinearMap.adjoint_adjoint]
theorem adjoint_euclideanSumInr : LinearMap.adjoint (euclideanSumInr α β) = euclideanSumSnd α β := by
  symm; rw [LinearMap.eq_adjoint_iff]; intro x y
  rw [← inner_conj_symm (euclideanSumSnd α β x) y, ← inner_euclideanSumInr y x, inner_conj_symm]
theorem adjoint_euclideanSumSnd : LinearMap.adjoint (euclideanSumSnd α β) = euclideanSumInr α β := by
  rw [← adjoint_euclideanSumInr, LinearMap.adjoint_adjoint]
theorem inner_sumInl_sumInr_eq_zero (x : EuclideanSpace ℂ α) (y : EuclideanSpace ℂ β) :
    ⟪euclideanSumInl α β x, euclideanSumInr α β y⟫_ℂ = 0 := by
  rw [inner_euclideanSumInl, euclideanSumFst_inr_apply, inner_zero_right]
theorem inner_sumInr_sumInl_eq_zero (y : EuclideanSpace ℂ β) (x : EuclideanSpace ℂ α) :
    ⟪euclideanSumInr α β y, euclideanSumInl α β x⟫_ℂ = 0 := by
  rw [inner_euclideanSumInr, euclideanSumSnd_inl_apply, inner_zero_right]
theorem euclideanSumInl_isometry (x y : EuclideanSpace ℂ α) :
    ⟪euclideanSumInl α β x, euclideanSumInl α β y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [inner_euclideanSumInl, euclideanSumFst_inl_apply]
theorem euclideanSumInr_isometry (x y : EuclideanSpace ℂ β) :
    ⟪euclideanSumInr α β x, euclideanSumInr α β y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [inner_euclideanSumInr, euclideanSumSnd_inr_apply]

end
end QuantumFoundations.Naimark.BinaryImpl
