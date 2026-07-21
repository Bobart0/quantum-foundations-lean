import Gleason.Busch.Effects
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
**FR.** # Définitions W0 — construction de Bargmann (§3–§5)

Toutes les définitions sont **totales** (pattern « définition totale + valeur
poubelle », cf. CLAUDE.md) : jamais de preuve prise en argument. La dimension `n`
est explicite pour `e`/`refVec` (rien d'autre ne permet de l'inférer) et implicite
partout où un `T : H n → H n` la fixe déjà.

Convention (Bargmann §3) : `𝒫 := e⊥` (ici `InPerp`, une `Prop`, JAMAIS un
`Submodule` — leçon N5/tentatives 1-2 de Naimark). `U` est construit par une
formule fermée (§5) ; le théorème de Wigner est un énoncé de COMPARAISON sur la
sphère, jamais une extension depuis `𝒫` ou depuis une base.

**EN.** # Definitions W0 — Bargmann's construction (§3–§5)

All definitions are total, following the “total definition + junk value”
pattern described in CLAUDE.md: no proof is ever passed as an argument. The
dimension n is explicit for e/refVec, because nothing else determines
it, and implicit wherever a term T : H n → H n already fixes it.

Convention (Bargmann §3): 𝒫 := e⊥, represented here by InPerp, a Prop,
NEVER a Submodule—the lesson from N5 / Naimark attempts 1–2. U is
constructed by a closed formula (§5); Wigner's theorem is a COMPARISON
statement on the sphere, never an extension from 𝒫 or from a basis.
-/

namespace QuantumFoundations.Wigner

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/--
**FR.** Vecteur de référence `e := (1,0,…,0)`. Junk `0` si `n = 0`.

**EN.** Reference vector e := (1,0,…,0). Junk value 0 if n = 0.
-/
noncomputable def e (n : ℕ) : H n :=
  if h : 0 < n then
    haveI : NeZero n := ⟨h.ne'⟩
    EuclideanSpace.single (0 : Fin n) 1
  else 0

/--
**FR.** Image de `e` par `T` (noté `e'` chez Bargmann).

**EN.** Image of e under T (denoted e' by Bargmann).
-/
noncomputable def eImg (T : H n → H n) : H n := T (e n)

/--
**FR.** `𝒫 := e⊥`, comme condition `Prop` — jamais le type `Submodule`.

**EN.** 𝒫 := e⊥, as a Prop-valued condition—never the type Submodule.
-/
def InPerp (z : H n) : Prop := ⟪e n, z⟫_ℂ = 0

/--
**FR.** **Construction B de Bargmann §3** : `V z := γ⁻¹ • T w − e'`, où `w` est le
représentant unitaire de `e + z` et `γ := ⟪e', T w⟫`. Junk (division par `0`, valeur
`Mathlib`-standard) si `γ = 0` ou `z` hors domaine.

**EN.** Bargmann's Construction B, §3:
V z := γ⁻¹ • T w − e', where w is the unit representative of e + z and
γ := ⟪e', T w⟫. The value is junk—division by 0, using the standard Mathlib value—if γ = 0 or z lies outside the domain.
-/
noncomputable def V (T : H n → H n) (z : H n) : H n :=
  let w := (‖e n + z‖⁻¹ : ℂ) • (e n + z)
  let γ := ⟪eImg T, T w⟫_ℂ
  γ⁻¹ • T w - eImg T

/--
**FR.** Second vecteur de la base canonique, utilisé comme référence pour `chi`. Junk
`0` si `n < 2`.

**EN.** Second vector of the canonical basis, used as the reference for chi.
Junk value 0 if n < 2.
-/
noncomputable def refVec (n : ℕ) : H n :=
  if h : 2 ≤ n then EuclideanSpace.single (⟨1, by omega⟩ : Fin n) 1 else 0

/--
**FR.** Extraction directionnelle de `χ` le long de `f` (Bargmann §4, eq. 14).

**EN.** Directional extraction of χ along f (Bargmann §4, Eq. 14).
-/
def chidir (T : H n → H n) (f : H n) (α : ℂ) : ℂ := ⟪V T f, V T (α • f)⟫_ℂ

/--
**FR.** `χ`, défonctionnalisé : une fonction nue `ℂ → ℂ`, calculée le long de
`refVec`. Bundlé en `id`/`conj` uniquement à la frontière (W5).

**EN.** χ, defunctionalized as a bare function ℂ → ℂ, computed along
refVec. It is bundled as id/conj only at the boundary (W5).
-/
noncomputable def chi (T : H n → H n) (α : ℂ) : ℂ := chidir T (refVec n) α

/-- **Assemblage de Bargmann §5** : `U a := χ⟪e,a⟫ • e' + V(a − ⟪e,a⟫•e)`. -/
noncomputable def U (T : H n → H n) (a : H n) : H n :=
  chi T ⟪e n, a⟫_ℂ • eImg T + V T (a - ⟪e n, a⟫_ℂ • e n)

/--
**FR.** Hypothèse du théorème de Wigner : `T` préserve les probabilités de transition
sur les vecteurs unitaires. Aucune bijectivité supposée (Bargmann §1.2-§1.3).

**EN.** Hypothesis of Wigner's theorem: T preserves transition probabilities
on unit vectors. No bijectivity is assumed (Bargmann §1.2–§1.3).
-/
def IsWignerMap (T : H n → H n) : Prop :=
  ∀ x y : H n, ‖x‖ = 1 → ‖y‖ = 1 → ‖⟪T x, T y⟫_ℂ‖ = ‖⟪x, y⟫_ℂ‖

end
end QuantumFoundations.Wigner
