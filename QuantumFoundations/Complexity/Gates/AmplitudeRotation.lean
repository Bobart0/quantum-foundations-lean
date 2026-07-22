import QuantumFoundations.Complexity.Gates.ControlledBitFlip
import QuantumFoundations.Complexity.Models.Repetition.Interference
import QuantumFoundations.Complexity.Models.NoisyRepetition.Profiles

/-!
# C11e — Canonical single-qubit amplitude-rotation gate

Unlike `controlledBitFlipGate` (a pure permutation of computational-basis
configurations), a `NoiseProfile` requires genuine amplitude *mixing* at one
site: `|0⟩ ↦ keep|0⟩ + leak|1⟩` there, identity elsewhere.  Since
`Sites N d := EuclideanSpace ℂ ((Fin N) → Fin d)` is the flat
computational-basis representation (deliberately not a Mathlib tensor
product), there is no ready-made "act on one tensor factor" combinator to
reuse; the operator is built directly from existing per-site infrastructure:

* `sitesCell N t 0`/`sitesCell N t 1` (from the repetition model): the two
  orthogonal, complementary computational-basis cells at site `t`, with
  projectors `P0`/`P1`.
* `bitFlipUnitary N t` (from the repetition model): the involutive,
  self-adjoint linear isometry swapping the bit at site `t`.

The rotation is `T := keep • P0 + leak • (F ∘ P0) - conj leak • (F ∘ P1) +
conj keep • P1`.  Restricted to the `sitesCell N t 0` fiber this acts as
`keep • id + leak • F`, i.e. exactly `|0⟩ ↦ keep|0⟩ + leak|1⟩`; restricted to
`sitesCell N t 1` it acts as `-conj leak • F + conj keep • id`, the second
column of the `2×2` unitary matrix with columns `(keep, leak)` and
`(-conj leak, conj keep)` — unitary exactly because `‖keep‖² + ‖leak‖² = 1`.
Unitarity of the *lifted*, all-`N`-site operator `T` is verified directly: an
arbitrary vector splits as `x = x₀ + x₁` (`xᵢ := Pᵢ x`, orthogonal, using
`P0 + P1 = id` from `sitesCell_covers`/`sitesCell_ortho`), and expanding
`⟪Tx, Tx⟫` using `F`'s self-adjointness and cell-swapping property collapses
every cross term, leaving exactly `‖keep‖² + ‖leak‖² = 1` times `‖x₀‖² +
‖x₁‖²= ‖x‖²`.
-/

namespace QuantumFoundations.Complexity.Gates

open scoped InnerProductSpace Classical

open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel

noncomputable section

variable {N : ℕ}

/-! ## C11e.1 — `bitFlipUnitary` is an involutive, self-adjoint isometry -/

theorem bitFlipConfigurationEquiv_symm_eq_self (t : Fin N) :
    (bitFlipConfigurationEquiv N t).symm = bitFlipConfigurationEquiv N t := by
  apply Equiv.ext
  intro g
  apply (bitFlipConfigurationEquiv N t).injective
  rw [Equiv.apply_symm_apply]
  funext s
  by_cases hs : s = t
  · subst hs
    rw [bitFlipConfigurationEquiv_at, bitFlipConfigurationEquiv_at]
    simp
  · rw [bitFlipConfigurationEquiv_off N t s (bitFlipConfigurationEquiv N t g) hs,
      bitFlipConfigurationEquiv_off N t s g hs]

theorem bitFlipUnitary_symm_eq_self (t : Fin N) :
    (bitFlipUnitary N t).symm = bitFlipUnitary N t := by
  unfold bitFlipUnitary
  rw [LinearIsometryEquiv.piLpCongrLeft_symm, bitFlipConfigurationEquiv_symm_eq_self]

theorem bitFlipUnitary_self_adjoint (t : Fin N) (u v : Sites N 2) :
    ⟪bitFlipUnitary N t u, v⟫_ℂ = ⟪u, bitFlipUnitary N t v⟫_ℂ := by
  conv_lhs => rw [← (bitFlipUnitary N t).apply_symm_apply v]
  rw [bitFlipUnitary_symm_eq_self, (bitFlipUnitary N t).inner_map_map]

/-- `bitFlipUnitary` sends the computational cell at bit `b` into the cell
at bit `swap 0 1 b`: it exchanges the two cells at site `t`. -/
theorem bitFlip_maps_cell (t : Fin N) (b : Fin 2) (x : Sites N 2) (hx : x ∈ sitesCell N t b) :
    bitFlipUnitary N t x ∈ sitesCell N t (Equiv.swap (0 : Fin 2) 1 b) := by
  have hmap : Submodule.map (bitFlipUnitary N t).toLinearIsometry.toLinearMap (sitesCell N t b) ≤
      sitesCell N t (Equiv.swap (0 : Fin 2) 1 b) := by
    unfold sitesCell
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro y ⟨x', ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨bitFlipConfigurationEquiv N t g, ?_, ?_⟩
    · show bitFlipConfigurationEquiv N t g t = Equiv.swap (0 : Fin 2) 1 b
      rw [bitFlipConfigurationEquiv_at, hg]
    · exact (bitFlipUnitary_configurationBasis N t g).symm
  exact hmap ⟨x, hx, rfl⟩

/-! ## C11e.2 — The two computational cells at a site resolve the identity -/

/-- The two orthogonal computational cells at site `t` sum to the
identity: `P0 + P1 = id`, the additive counterpart of `sitesCell_covers`
(sup `= ⊤`) and `sitesCell_ortho` (orthogonality). -/
theorem sitesCell_starProjection_add (t : Fin N) (x : Sites N 2) :
    (sitesCell N t 0).starProjection x + (sitesCell N t 1).starProjection x = x := by
  have key : ∀ (A B : Submodule ℂ (Sites N 2)) [A.HasOrthogonalProjection]
      [B.HasOrthogonalProjection],
      A ⟂ B → A ⊔ B = ⊤ → A.starProjection x + B.starProjection x = x := by
    intro A B _ _ hAB hsup
    have heq : (A ⊔ B).starProjection x = A.starProjection x + B.starProjection x := by
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      · exact Submodule.add_mem_sup (Submodule.starProjection_apply_mem A x)
          (Submodule.starProjection_apply_mem B x)
      · intro w hw
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
        rw [inner_add_right]
        have h1 : ⟪x - (A.starProjection x + B.starProjection x), a⟫_ℂ = 0 := by
          rw [show x - (A.starProjection x + B.starProjection x) =
              (x - A.starProjection x) - B.starProjection x from by abel,
            inner_sub_left,
            Submodule.starProjection_inner_eq_zero (K := A) x a ha,
            Submodule.isOrtho_iff_inner_eq.mp hAB.symm _
              (Submodule.starProjection_apply_mem B x) _ ha]
          simp
        have h2 : ⟪x - (A.starProjection x + B.starProjection x), b⟫_ℂ = 0 := by
          rw [show x - (A.starProjection x + B.starProjection x) =
              (x - B.starProjection x) - A.starProjection x from by abel,
            inner_sub_left,
            Submodule.starProjection_inner_eq_zero (K := B) x b hb,
            Submodule.isOrtho_iff_inner_eq.mp hAB _
              (Submodule.starProjection_apply_mem A x) _ hb]
          simp
        rw [h1, h2, add_zero]
    have hmem : x ∈ A ⊔ B := hsup ▸ Submodule.mem_top
    rw [← heq]
    exact Submodule.starProjection_eq_self_iff.mpr hmem
  exact key (sitesCell N t 0) (sitesCell N t 1) (sitesCell_ortho t (by decide)) (sitesCell_covers t)

/-! ## C11e.3 — The linear map and its isometry property -/

/-- The `2 × 2` amplitude-rotation lifted to all `N` sites at site `t`:
`keep • P0 + leak • (F ∘ P0) - conj leak • (F ∘ P1) + conj keep • P1`. -/
def prepLinearMap (p : NoiseProfile) (t : Fin N) : Sites N 2 →ₗ[ℂ] Sites N 2 :=
  p.keep • (sitesCell N t 0).starProjection.toLinearMap +
    p.leak • ((bitFlipUnitary N t).toLinearIsometry.toLinearMap ∘ₗ
      (sitesCell N t 0).starProjection.toLinearMap) +
    (-(starRingEnd ℂ p.leak)) • ((bitFlipUnitary N t).toLinearIsometry.toLinearMap ∘ₗ
      (sitesCell N t 1).starProjection.toLinearMap) +
    (starRingEnd ℂ p.keep) • (sitesCell N t 1).starProjection.toLinearMap

theorem prepLinearMap_apply (p : NoiseProfile) (t : Fin N) (x : Sites N 2) :
    prepLinearMap p t x =
      p.keep • (sitesCell N t 0).starProjection x
        + p.leak • bitFlipUnitary N t ((sitesCell N t 0).starProjection x)
        + (-(starRingEnd ℂ p.leak)) • bitFlipUnitary N t ((sitesCell N t 1).starProjection x)
        + (starRingEnd ℂ p.keep) • (sitesCell N t 1).starProjection x := rfl

/-- The rotation is an isometry: the key computation of C11e.  Splitting
`x = x₀ + x₁` along the two cells and expanding `⟪Tx, Tx⟫` via `F`'s
self-adjointness, the cell-swapping property, and `p.norm_sq` collapses
every cross term, leaving exactly `‖x‖²`. -/
theorem prepLinearMap_isometry (p : NoiseProfile) (t : Fin N) (x : Sites N 2) :
    ‖prepLinearMap p t x‖ = ‖x‖ := by
  rw [prepLinearMap_apply]
  set x0 := (sitesCell N t 0).starProjection x with hx0def
  set x1 := (sitesCell N t 1).starProjection x with hx1def
  have hx01 : x0 + x1 = x := sitesCell_starProjection_add t x
  have hx0mem : x0 ∈ sitesCell N t 0 := Submodule.starProjection_apply_mem _ x
  have hx1mem : x1 ∈ sitesCell N t 1 := Submodule.starProjection_apply_mem _ x
  have hFx0mem : bitFlipUnitary N t x0 ∈ sitesCell N t 1 := by
    have := bitFlip_maps_cell t 0 x0 hx0mem; simpa using this
  have hFx1mem : bitFlipUnitary N t x1 ∈ sitesCell N t 0 := by
    have := bitFlip_maps_cell t 1 x1 hx1mem; simpa using this
  have hortho01 : ⟪x0, x1⟫_ℂ = 0 :=
    Submodule.isOrtho_iff_inner_eq.mp (sitesCell_ortho t (by decide)) _ hx0mem _ hx1mem
  have horthoFx0x0 : ⟪x0, bitFlipUnitary N t x0⟫_ℂ = 0 :=
    Submodule.isOrtho_iff_inner_eq.mp (sitesCell_ortho t (by decide)) _ hx0mem _ hFx0mem
  have horthoFx1x1 : ⟪x1, bitFlipUnitary N t x1⟫_ℂ = 0 :=
    Submodule.isOrtho_iff_inner_eq.mp
      (sitesCell_ortho t (by decide : (1 : Fin 2) ≠ 0)) _ hx1mem _ hFx1mem
  have horthoFxFx : ⟪bitFlipUnitary N t x0, bitFlipUnitary N t x1⟫_ℂ = 0 :=
    Submodule.isOrtho_iff_inner_eq.mp (sitesCell_ortho t (by decide)) _ hFx0mem _ hFx1mem
  have hadj1 : ⟪bitFlipUnitary N t x0, x1⟫_ℂ = ⟪x0, bitFlipUnitary N t x1⟫_ℂ :=
    bitFlipUnitary_self_adjoint t x0 x1
  have hadj2 : ⟪bitFlipUnitary N t x1, x0⟫_ℂ = ⟪x1, bitFlipUnitary N t x0⟫_ℂ :=
    bitFlipUnitary_self_adjoint t x1 x0
  have hortho10 : ⟪x1, x0⟫_ℂ = 0 := by
    rw [← inner_conj_symm x1 x0, hortho01]; simp
  have horthoFx0x0' : ⟪bitFlipUnitary N t x0, x0⟫_ℂ = 0 := by
    rw [← inner_conj_symm (bitFlipUnitary N t x0) x0, horthoFx0x0]; simp
  have horthoFx1x1' : ⟪bitFlipUnitary N t x1, x1⟫_ℂ = 0 := by
    rw [← inner_conj_symm (bitFlipUnitary N t x1) x1, horthoFx1x1]; simp
  have horthoFxFx' : ⟪bitFlipUnitary N t x1, bitFlipUnitary N t x0⟫_ℂ = 0 := by
    rw [← inner_conj_symm (bitFlipUnitary N t x1) (bitFlipUnitary N t x0), horthoFxFx]; simp
  have ha : p.keep * (starRingEnd ℂ p.keep) = ((‖p.keep‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; norm_cast
  have hb : p.leak * (starRingEnd ℂ p.leak) = ((‖p.leak‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; norm_cast
  have hcast : ((‖p.keep‖ ^ 2 : ℝ) : ℂ) + ((‖p.leak‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_add, p.norm_sq]; norm_num
  have hsum : p.keep * starRingEnd ℂ p.keep + p.leak * starRingEnd ℂ p.leak = 1 := by
    rw [ha, hb]; exact hcast
  have hnorm0 : ‖bitFlipUnitary N t x0‖ = ‖x0‖ := (bitFlipUnitary N t).norm_map x0
  have hnorm1 : ‖bitFlipUnitary N t x1‖ = ‖x1‖ := (bitFlipUnitary N t).norm_map x1
  have hFselfx0 : ⟪bitFlipUnitary N t x0, bitFlipUnitary N t x0⟫_ℂ = ⟪x0, x0⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hnorm0]
  have hFselfx1 : ⟪bitFlipUnitary N t x1, bitFlipUnitary N t x1⟫_ℂ = ⟪x1, x1⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hnorm1]
  have hTT : ⟪p.keep • x0 + p.leak • bitFlipUnitary N t x0
        + (-(starRingEnd ℂ p.leak)) • bitFlipUnitary N t x1 + (starRingEnd ℂ p.keep) • x1,
      p.keep • x0 + p.leak • bitFlipUnitary N t x0
        + (-(starRingEnd ℂ p.leak)) • bitFlipUnitary N t x1 + (starRingEnd ℂ p.keep) • x1⟫_ℂ
      = ⟪x0, x0⟫_ℂ + ⟪x1, x1⟫_ℂ := by
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      hortho01, hortho10, horthoFx0x0, horthoFx0x0', horthoFx1x1, horthoFx1x1',
      horthoFxFx, horthoFxFx', hadj1, hadj2, hFselfx0, hFselfx1, map_neg,
      neg_mul, Complex.conj_conj]
    linear_combination (⟪x0, x0⟫_ℂ + ⟪x1, x1⟫_ℂ) * hsum
  have hxx : ⟪x0, x0⟫_ℂ + ⟪x1, x1⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [← hx01, inner_add_left, inner_add_right, inner_add_right, hortho01, hortho10]
    ring
  rw [hxx] at hTT
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hTT
  have hcast2 : (‖p.keep • x0 + p.leak • bitFlipUnitary N t x0
      + (-(starRingEnd ℂ p.leak)) • bitFlipUnitary N t x1 + (starRingEnd ℂ p.keep) • x1‖) ^ 2
      = (‖x‖) ^ 2 := by exact_mod_cast hTT
  nlinarith [hcast2, norm_nonneg (p.keep • x0 + p.leak • bitFlipUnitary N t x0
      + (-(starRingEnd ℂ p.leak)) • bitFlipUnitary N t x1 + (starRingEnd ℂ p.keep) • x1),
    norm_nonneg x]

/-- The rotation as a `LinearIsometry`. -/
def prepIsometry (p : NoiseProfile) (t : Fin N) : Sites N 2 →ₗᵢ[ℂ] Sites N 2 :=
  ⟨prepLinearMap p t, prepLinearMap_isometry p t⟩

/-- The rotation as a `LinearIsometryEquiv`: bijective since it is an
isometric endomorphism of a finite-dimensional space. -/
def prepUnitary (p : NoiseProfile) (t : Fin N) : Sites N 2 ≃ₗᵢ[ℂ] Sites N 2 :=
  (prepIsometry p t).toLinearIsometryEquiv rfl

theorem prepUnitary_apply (p : NoiseProfile) (t : Fin N) (x : Sites N 2) :
    prepUnitary p t x = prepLinearMap p t x := rfl

/-! ## C11e.4 — Exact action on computational-basis configurations -/

/-- On the `sitesCell N t 0` fiber the rotation acts exactly as the first
column of the `2 × 2` matrix: `|0⟩ ↦ keep|0⟩ + leak|1⟩`. -/
theorem prepUnitary_single_of_zero (p : NoiseProfile) (t : Fin N) (g : Fin N → Fin 2)
    (hg : g t = 0) :
    prepUnitary p t (EuclideanSpace.single g (1 : ℂ)) =
      p.keep • EuclideanSpace.single g 1
        + p.leak • EuclideanSpace.single (bitFlipConfigurationEquiv N t g) 1 := by
  rw [prepUnitary_apply, prepLinearMap_apply]
  rw [show ((sitesCell N t 0).starProjection (EuclideanSpace.single g (1:ℂ))
      : Sites N 2) = EuclideanSpace.single g 1 from by
    rw [show (EuclideanSpace.single g (1:ℂ) : Sites N 2) = configurationBasis g from rfl,
      sitesCell_starProjection_configurationBasis, if_pos hg]]
  rw [show ((sitesCell N t 1).starProjection (EuclideanSpace.single g (1:ℂ))
      : Sites N 2) = 0 from by
    rw [show (EuclideanSpace.single g (1:ℂ) : Sites N 2) = configurationBasis g from rfl,
      sitesCell_starProjection_configurationBasis, if_neg (by rw [hg]; decide)]]
  rw [show (bitFlipUnitary N t) (EuclideanSpace.single g (1:ℂ)) =
      EuclideanSpace.single (bitFlipConfigurationEquiv N t g) 1 from
    bitFlipUnitary_configurationBasis N t g]
  simp only [map_zero]
  module

/-- On the `sitesCell N t 1` fiber the rotation acts exactly as the second
column: `|1⟩ ↦ -conj leak |0⟩ + conj keep |1⟩`. -/
theorem prepUnitary_single_of_one (p : NoiseProfile) (t : Fin N) (g : Fin N → Fin 2)
    (hg : g t = 1) :
    prepUnitary p t (EuclideanSpace.single g (1 : ℂ)) =
      (-(starRingEnd ℂ p.leak)) • EuclideanSpace.single (bitFlipConfigurationEquiv N t g) 1
        + (starRingEnd ℂ p.keep) • EuclideanSpace.single g 1 := by
  rw [prepUnitary_apply, prepLinearMap_apply]
  rw [show ((sitesCell N t 1).starProjection (EuclideanSpace.single g (1:ℂ))
      : Sites N 2) = EuclideanSpace.single g 1 from by
    rw [show (EuclideanSpace.single g (1:ℂ) : Sites N 2) = configurationBasis g from rfl,
      sitesCell_starProjection_configurationBasis, if_pos hg]]
  rw [show ((sitesCell N t 0).starProjection (EuclideanSpace.single g (1:ℂ))
      : Sites N 2) = 0 from by
    rw [show (EuclideanSpace.single g (1:ℂ) : Sites N 2) = configurationBasis g from rfl,
      sitesCell_starProjection_configurationBasis, if_neg (by rw [hg]; decide)]]
  rw [show (bitFlipUnitary N t) (EuclideanSpace.single g (1:ℂ)) =
      EuclideanSpace.single (bitFlipConfigurationEquiv N t g) 1 from
    bitFlipUnitary_configurationBasis N t g]
  simp only [map_zero]
  module

/-! ## C11e.5 — Locality -/

/-- Auxiliary: if `g` agrees with `k` off `t` and `g`'s bit at `t` equals the
flipped value of `k`'s bit at `t`, then `g` is exactly the bit-flip of `k`. -/
private theorem bitFlip_eq_of_agreesOff_and_val (t : Fin N) (g k : Fin N → Fin 2)
    (hoff : AgreesOff ({t} : Finset (Fin N)) g k) (hval : g t = Equiv.swap (0 : Fin 2) 1 (k t)) :
    g = bitFlipConfigurationEquiv N t k := by
  funext s
  by_cases hst : s = t
  · subst hst; rw [bitFlipConfigurationEquiv_at, hval]
  · rw [bitFlipConfigurationEquiv_off N t s k hst]
    exact hoff s (by simpa using hst)

/-- The rotation is local to the single site `t`: its matrix elements
depend only on the restrictions of the two configurations to `{t}`, i.e. on
`g t` and `k t`, and vanish whenever the configurations differ elsewhere. -/
theorem prepUnitary_local (p : NoiseProfile) (t : Fin N) :
    IsLocalTo (prepUnitary p t).toLinearIsometry.toLinearMap ({t} : Finset (Fin N)) := by
  refine ⟨fun gl kl =>
    if kl ⟨t, by simp⟩ = 0 then (if gl ⟨t, by simp⟩ = 0 then p.keep else p.leak)
    else (if gl ⟨t, by simp⟩ = 0 then -(starRingEnd ℂ p.leak) else starRingEnd ℂ p.keep), ?_⟩
  intro g k
  change ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N 2),
    prepUnitary p t (EuclideanSpace.single k 1)⟫_ℂ = _
  by_cases hk0 : k t = 0
  · rw [prepUnitary_single_of_zero p t k hk0]
    rw [inner_add_right, inner_smul_right, inner_smul_right,
      EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul, PiLp.single_apply]
    by_cases hgk : g = k
    · subst hgk
      have hne : g ≠ bitFlipConfigurationEquiv N t g := by
        intro heq
        have := congrFun heq t
        rw [bitFlipConfigurationEquiv_at, hk0] at this
        simp at this
      simp [hne, AgreesOff, hk0]
    · by_cases hgf : g = bitFlipConfigurationEquiv N t k
      · have hoff : AgreesOff ({t} : Finset (Fin N)) g k := by
          rw [hgf]
          intro s hs
          exact bitFlipConfigurationEquiv_off N t s k (by simpa using hs)
        have hgt : g t = 1 := by rw [hgf, bitFlipConfigurationEquiv_at, hk0]; decide
        simp [hgk, hgf.symm, hoff, hk0, hgt]
      · have hoffnot : ¬ AgreesOff ({t} : Finset (Fin N)) g k := by
          intro hoff
          rcases (by omega : g t = 0 ∨ g t = 1) with hgt0 | hgt1
          · apply hgk
            funext s
            by_cases hst : s = t
            · subst hst; rw [hgt0, hk0]
            · exact hoff s (by simpa using hst)
          · apply hgf
            apply bitFlip_eq_of_agreesOff_and_val t g k hoff
            rw [hgt1, hk0]; decide
        simp [hgk, hgf, hoffnot]
  · have hk1 : k t = 1 := by omega
    rw [prepUnitary_single_of_one p t k hk1]
    rw [inner_add_right, inner_smul_right, inner_smul_right,
      EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul, PiLp.single_apply]
    by_cases hgk : g = k
    · subst hgk
      have hne : g ≠ bitFlipConfigurationEquiv N t g := by
        intro heq
        have := congrFun heq t
        rw [bitFlipConfigurationEquiv_at, hk1] at this
        simp at this
      simp [hne, AgreesOff, hk1]
    · by_cases hgf : g = bitFlipConfigurationEquiv N t k
      · have hoff : AgreesOff ({t} : Finset (Fin N)) g k := by
          rw [hgf]
          intro s hs
          exact bitFlipConfigurationEquiv_off N t s k (by simpa using hs)
        have hgt : g t = 0 := by rw [hgf, bitFlipConfigurationEquiv_at, hk1]; decide
        simp [hgk, hgf.symm, hoff, hk1, hgt]
      · have hoffnot : ¬ AgreesOff ({t} : Finset (Fin N)) g k := by
          intro hoff
          rcases (by omega : g t = 0 ∨ g t = 1) with hgt0 | hgt1
          · apply hgf
            apply bitFlip_eq_of_agreesOff_and_val t g k hoff
            rw [hgt0, hk1]; decide
          · apply hgk
            funext s
            by_cases hst : s = t
            · subst hst; rw [hgt1, hk1]
            · exact hoff s (by simpa using hst)
        simp [hgk, hgf, hoffnot]

/-! ## C11e.6 — The gate -/

/-- The canonical single-site amplitude-rotation gate implementing a
`NoiseProfile` at site `t`. -/
def amplitudeRotationGate (p : NoiseProfile) (t : Fin N) : TwoLocalGate N 2 where
  unitary := prepUnitary p t
  support := {t}
  locality := prepUnitary_local p t
  support_card_le_two := by simp

@[simp] theorem amplitudeRotationGate_support (p : NoiseProfile) (t : Fin N) :
    (amplitudeRotationGate p t).support = {t} := rfl

/-! ## C11e.7 — Action on `H`-transported configuration branches -/

theorem amplitudeRotationGate_maps_configurationBranch_of_zero (p : NoiseProfile) (t : Fin N)
    (g : Fin N → Fin 2) (hg : g t = 0) :
    Circuit.evalOnH [amplitudeRotationGate p t] (sitesEquivR N) (configurationBranch N g) =
      p.keep • configurationBranch N g
        + p.leak • configurationBranch N (bitFlipConfigurationEquiv N t g) := by
  show Circuit.evalOnH [amplitudeRotationGate p t] (sitesEquivR N)
      ((sitesEquivR N).symm (EuclideanSpace.single g (1 : ℂ))) =
    p.keep • (sitesEquivR N).symm (EuclideanSpace.single g 1)
      + p.leak • (sitesEquivR N).symm (EuclideanSpace.single (bitFlipConfigurationEquiv N t g) 1)
  apply (sitesEquivR N).injective
  simp [Circuit.evalOnH]
  exact prepUnitary_single_of_zero p t g hg

theorem amplitudeRotationGate_maps_configurationBranch_of_one (p : NoiseProfile) (t : Fin N)
    (g : Fin N → Fin 2) (hg : g t = 1) :
    Circuit.evalOnH [amplitudeRotationGate p t] (sitesEquivR N) (configurationBranch N g) =
      (-(starRingEnd ℂ p.leak)) • configurationBranch N (bitFlipConfigurationEquiv N t g)
        + (starRingEnd ℂ p.keep) • configurationBranch N g := by
  show Circuit.evalOnH [amplitudeRotationGate p t] (sitesEquivR N)
      ((sitesEquivR N).symm (EuclideanSpace.single g (1 : ℂ))) =
    (-(starRingEnd ℂ p.leak)) •
        (sitesEquivR N).symm (EuclideanSpace.single (bitFlipConfigurationEquiv N t g) 1)
      + (starRingEnd ℂ p.keep) • (sitesEquivR N).symm (EuclideanSpace.single g 1)
  apply (sitesEquivR N).injective
  simp [Circuit.evalOnH]
  rw [← neg_smul]
  exact prepUnitary_single_of_one p t g hg

end

end QuantumFoundations.Complexity.Gates
