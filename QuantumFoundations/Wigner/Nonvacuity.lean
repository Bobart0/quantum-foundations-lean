import QuantumFoundations.Wigner.Defs

/-!
# Nonvacuity — l'énoncé `wigner` n'est ni vacueux ni mal câblé

Contrairement à Naimark (`POVM` est une structure), `wigner` est un théorème avec
hypothèse `IsWignerMap T` : la discipline de non-vacuité ici consiste à exhiber,
pour un `T` concret satisfaisant `IsWignerMap`, un témoin direct de CHACUNE des
deux branches de la conclusion — preuve que la disjonction n'est pas mal câblée
(p.ex. qu'une seule branche ne serait jamais atteignable). `T := id` habite la
branche unitaire ; `T := conjCoords` (conjugaison composante par composante)
habite la branche antiunitaire.
-/

namespace QuantumFoundations.Wigner

open scoped InnerProductSpace
open Gleason

noncomputable section

/-- Conjugaison composante par composante sur `H n`. -/
def conjCoords (n : ℕ) (x : H n) : H n := WithLp.toLp 2 (fun i => starRingEnd ℂ (x i))

@[simp] theorem conjCoords_apply (n : ℕ) (x : H n) (i : Fin n) :
    (conjCoords n x) i = starRingEnd ℂ (x i) := rfl

theorem inner_conjCoords (n : ℕ) (x y : H n) :
    ⟪conjCoords n x, conjCoords n y⟫_ℂ = starRingEnd ℂ ⟪x, y⟫_ℂ := by
  simp only [PiLp.inner_apply, conjCoords_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

/-- `conjCoords` comme application conj-semilinéaire. -/
def conjCoordsLM (n : ℕ) : H n →ₛₗ[starRingEnd ℂ] H n where
  toFun := conjCoords n
  map_add' x y := by
    apply WithLp.ext_iff .. |>.mpr; funext i; simp [conjCoords, map_add]
  map_smul' c x := by
    apply WithLp.ext_iff .. |>.mpr; funext i; simp [conjCoords]

theorem conjCoordsLM_involutive (n : ℕ) : Function.Involutive (conjCoordsLM n) := by
  intro x; apply WithLp.ext_iff .. |>.mpr; funext i; simp [conjCoordsLM, conjCoords]

theorem norm_conjCoords (n : ℕ) (x : H n) : ‖conjCoords n x‖ = ‖x‖ := by
  have h1 : (‖conjCoords n x‖ : ℝ) ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_conjCoords]
    simp
  nlinarith [norm_nonneg (conjCoords n x), norm_nonneg x, sq_nonneg (‖conjCoords n x‖ - ‖x‖)]

/-- `conjCoords`, bundlé en isométrie conj-semilinéaire (antiunitaire). -/
noncomputable def conjCoordsEquiv (n : ℕ) : H n ≃ₛₗᵢ[starRingEnd ℂ] H n where
  toLinearEquiv := LinearEquiv.ofBijective (conjCoordsLM n) (conjCoordsLM_involutive n).bijective
  norm_map' x := norm_conjCoords n x

/-- Témoin branche unitaire : l'identité préserve trivialement les probabilités
de transition. -/
example : IsWignerMap (id : H 2 → H 2) := fun _ _ _ _ => rfl

example :
    ∃ U' : H 2 ≃ₗᵢ[ℂ] H 2, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ (id : H 2 → H 2) x = c • U' x :=
  ⟨LinearIsometryEquiv.refl ℂ (H 2), fun x _ => ⟨1, by norm_num, by simp⟩⟩

/-- Témoin branche antiunitaire : la conjugaison composante par composante
préserve les probabilités de transition (`⟪conj x, conj y⟫ = conj ⟪x,y⟫`, même
module). -/
example : IsWignerMap (conjCoords 2) := by
  intro x y hx hy
  rw [inner_conjCoords, RCLike.norm_conj]

example :
    ∃ U' : H 2 ≃ₛₗᵢ[starRingEnd ℂ] H 2,
      ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ conjCoords 2 x = c • U' x :=
  ⟨conjCoordsEquiv 2, fun x _ => ⟨1, by norm_num, by rw [one_smul]; rfl⟩⟩

end
end QuantumFoundations.Wigner
