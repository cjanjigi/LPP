/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportTilt
import Busemann.Geometry.StrictSupportFaceSeparation
import Busemann.Geometry.SupportIdentities
import Busemann.Geometry.SupportOrder
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Bases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! One-sided sequential continuity of the actual extreme support tilts. -/

public section

open Filter LPPDifferentiability
open scoped NNReal Topology

namespace LPP.Busemann

private theorem interiorDirection_eq_of_first_coord
    (ξ η : InteriorDirection) (h : (ξ.1.1 : ℝ) = (η.1.1 : ℝ)) : ξ = η := by
  apply Subtype.ext
  apply Prod.ext
  · exact NNReal.coe_injective h
  · apply NNReal.coe_injective
    linarith only [ξ.2.2.2, η.2.2.2, h]

private theorem second_coord_le_of_first_coord_le
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (h k : SupportTilt g) (hfirst : h.1.1 ≤ k.1.1) : k.1.2 ≤ h.1.2 := by
  rcases eq_or_lt_of_le hfirst with heq | hlt
  · have hhk : h = k := (supportTilt_coordinate_order g hhom h k).2 heq
    rw [hhk]
  · exact le_of_lt ((supportTilt_coordinate_order g hhom h k).1 hlt).1

private theorem supportsAt_of_tendsto
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (ξs : ℕ → InteriorDirection) (hs : ℕ → SupportTilt g)
    (ξ : InteriorDirection) (p : ℝ × ℝ)
    (hξ : Tendsto ξs atTop (𝓝 ξ))
    (hp : Tendsto (fun n => (hs n).1) atTop (𝓝 p))
    (hsupport : ∀ n, SupportsAt g (ξs n) (hs n).1) :
    SupportsAt g ξ p := by
  intro z
  let F : InteriorDirection × (ℝ × ℝ) → ℝ := fun w =>
    (-w.2.1) * ((w.1.1.1 : ℝ) - (z.1 : ℝ)) +
      (-w.2.2) * ((w.1.1.2 : ℝ) - (z.2 : ℝ))
  let G : InteriorDirection × (ℝ × ℝ) → ℝ := fun w => g w.1.1 - g z
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hG : Continuous G := by
    dsimp [G]
    fun_prop
  have hpair : Tendsto (fun n => (ξs n, (hs n).1)) atTop (𝓝 (ξ, p)) :=
    by simpa only [nhds_prod_eq] using hξ.prodMk hp
  have hle : ∀ n, F (ξs n, (hs n).1) ≤ G (ξs n, (hs n).1) := by
    intro n
    exact hsupport n z
  exact le_of_tendsto_of_tendsto' (hF.tendsto (ξ, p) |>.comp hpair)
    (hG.tendsto (ξ, p) |>.comp hpair) hle

private theorem support_tilt_tendsto_of_compact_unique_limit
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (ξs : ℕ → InteriorDirection) (hs : ℕ → SupportTilt g)
    (ξ : InteriorDirection) (target : SupportTilt g)
    (hξ : Tendsto ξs atTop (𝓝 ξ))
    (hsupport : ∀ n, SupportsAt g (ξs n) (hs n).1)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hmem : ∀ᶠ n in atTop, (hs n).1 ∈ K)
    (hunique : ∀ p ∈ K, SupportsAt g ξ p → p = target.1) :
    Tendsto hs atTop (𝓝 target) := by
  have hraw : Tendsto (fun n => (hs n).1) atTop (𝓝 target.1) :=
    hK.tendsto_nhds_of_unique_mapClusterPt hmem (by
      intro p hp hcluster
      obtain ⟨φ, hφ, hpφ⟩ := MapClusterPt.tendsto_subseq hcluster
      have hξφ : Tendsto (ξs ∘ φ) atTop (𝓝 ξ) := hξ.comp hφ.tendsto_atTop
      have hsuppφ : ∀ n, SupportsAt g ((ξs ∘ φ) n) ((hs ∘ φ) n).1 :=
        fun n => hsupport (φ n)
      have hsupportP := supportsAt_of_tendsto g hgcont (ξs ∘ φ) (hs ∘ φ)
        ξ p hξφ hpφ hsuppφ
      exact hunique p hp hsupportP)
  exact tendsto_subtype_rng.2 hraw

private theorem support_first_coord_le_of_direction_le
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (q t : InteriorDirection) (h k : SupportTilt g)
    (hqt : (q.1.1 : ℝ) ≤ (t.1.1 : ℝ))
    (hq : SupportsAt g q h.1) (ht : SupportsAt g t k.1)
    (heq_tilt : q = t → h = k) :
    h.1.1 ≤ k.1.1 := by
  rcases eq_or_lt_of_le hqt with heq | hlt
  · have hdir : q = t := interiorDirection_eq_of_first_coord q t heq
    rw [heq_tilt hdir]
  · exact support_first_coord_le_of_direction_lt g hhom q t h k hlt hq ht

/-- The actual minimal first-coordinate support is continuous under approach
from the left, including sequences that sometimes equal the target direction. -/
theorem extreme_left_tilt_tendsto_of_tendsto_from_left
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z)
    (hL hR : InteriorDirection → SupportTilt g)
    (hExtreme : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1)
    (ξ : InteriorDirection) (ξs : ℕ → InteriorDirection)
    (hside : ∀ n, ((ξs n).1.1 : ℝ) ≤ (ξ.1.1 : ℝ))
    (hlim : Tendsto ξs atTop (𝓝 ξ)) :
    Tendsto (fun n => hL (ξs n)) atTop (𝓝 (hL ξ)) := by
  have _hconc := hconc ξ.1 ξ.1 1 0 (by simp)
  by_cases hex : ∃ n, ((ξs n).1.1 : ℝ) < (ξ.1.1 : ℝ)
  · obtain ⟨n₀, hn₀⟩ := hex
    let a : SupportTilt g := hL (ξs n₀)
    let b : SupportTilt g := hL ξ
    have hcoord : Continuous (fun q : InteriorDirection => (q.1.1 : ℝ)) := by fun_prop
    have hevent : ∀ᶠ n in atTop, ((ξs n₀).1.1 : ℝ) < ((ξs n).1.1 : ℝ) :=
      hlim.eventually ((isOpen_lt continuous_const hcoord).mem_nhds hn₀)
    have hupper (n : ℕ) : (hL (ξs n)).1.1 ≤ b.1.1 := by
      exact support_first_coord_le_of_direction_le g hhom (ξs n) ξ
        (hL (ξs n)) b (hside n) (hExtreme (ξs n)).1 (hExtreme ξ).1
        (by intro hdir; simp only [hdir, b])
    have hlower : ∀ᶠ n in atTop, a.1.1 ≤ (hL (ξs n)).1.1 := by
      filter_upwards [hevent] with n hn
      exact support_first_coord_le_of_direction_lt g hhom (ξs n₀) (ξs n)
        a (hL (ξs n)) hn (hExtreme (ξs n₀)).1 (hExtreme (ξs n)).1
    let K : Set (ℝ × ℝ) := Set.Icc (a.1.1, b.1.2) (b.1.1, a.1.2)
    have hK : IsCompact K := isCompact_Icc
    have hmem : ∀ᶠ n in atTop, (hL (ξs n)).1 ∈ K := by
      filter_upwards [hlower] with n hlow
      have hup := hupper n
      have hsecondLow : b.1.2 ≤ (hL (ξs n)).1.2 :=
        second_coord_le_of_first_coord_le g hhom (hL (ξs n)) b hup
      have hsecondUp : (hL (ξs n)).1.2 ≤ a.1.2 :=
        second_coord_le_of_first_coord_le g hhom a (hL (ξs n)) hlow
      exact ⟨⟨hlow, hsecondLow⟩, ⟨hup, hsecondUp⟩⟩
    apply support_tilt_tendsto_of_compact_unique_limit g hgcont ξs
      (fun n => hL (ξs n)) ξ b hlim (fun n => (hExtreme (ξs n)).1)
      K hK hmem
    intro p hp hsupportP
    let k : SupportTilt g := ⟨p, ⟨ξ, hsupportP⟩⟩
    have hbmin : b.1.1 ≤ k.1.1 := ((hExtreme ξ).2.2 k hsupportP).1
    have hkle : k.1.1 ≤ b.1.1 := hp.2.1
    have hbk : b = k :=
      (supportTilt_coordinate_order g hhom b k).2 (le_antisymm hbmin hkle)
    exact (congrArg Subtype.val hbk).symm
  · have heq (n : ℕ) : ξs n = ξ := by
      apply interiorDirection_eq_of_first_coord
      exact le_antisymm (hside n) (le_of_not_gt (not_exists.mp hex n))
    have hf : (fun n => hL (ξs n)) = fun _ => hL ξ := by
      funext n
      rw [heq n]
    rw [hf]
    exact tendsto_const_nhds

/-- The actual maximal first-coordinate support is continuous under approach
from the right, including sequences that sometimes equal the target direction. -/
theorem extreme_right_tilt_tendsto_of_tendsto_from_right
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z)
    (hL hR : InteriorDirection → SupportTilt g)
    (hExtreme : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1)
    (ξ : InteriorDirection) (ξs : ℕ → InteriorDirection)
    (hside : ∀ n, (ξ.1.1 : ℝ) ≤ ((ξs n).1.1 : ℝ))
    (hlim : Tendsto ξs atTop (𝓝 ξ)) :
    Tendsto (fun n => hR (ξs n)) atTop (𝓝 (hR ξ)) := by
  have _hconc := hconc ξ.1 ξ.1 1 0 (by simp)
  by_cases hex : ∃ n, (ξ.1.1 : ℝ) < ((ξs n).1.1 : ℝ)
  · obtain ⟨n₀, hn₀⟩ := hex
    let a : SupportTilt g := hR ξ
    let b : SupportTilt g := hR (ξs n₀)
    have hcoord : Continuous (fun q : InteriorDirection => (q.1.1 : ℝ)) := by fun_prop
    have hevent : ∀ᶠ n in atTop, ((ξs n).1.1 : ℝ) < ((ξs n₀).1.1 : ℝ) :=
      hlim.eventually ((isOpen_lt hcoord continuous_const).mem_nhds hn₀)
    have hlower (n : ℕ) : a.1.1 ≤ (hR (ξs n)).1.1 := by
      exact support_first_coord_le_of_direction_le g hhom ξ (ξs n)
        a (hR (ξs n)) (hside n) (hExtreme ξ).2.1 (hExtreme (ξs n)).2.1
        (by intro hdir; simp only [← hdir, a])
    have hupper : ∀ᶠ n in atTop, (hR (ξs n)).1.1 ≤ b.1.1 := by
      filter_upwards [hevent] with n hn
      exact support_first_coord_le_of_direction_lt g hhom (ξs n) (ξs n₀)
        (hR (ξs n)) b hn (hExtreme (ξs n)).2.1 (hExtreme (ξs n₀)).2.1
    let K : Set (ℝ × ℝ) := Set.Icc (a.1.1, b.1.2) (b.1.1, a.1.2)
    have hK : IsCompact K := isCompact_Icc
    have hmem : ∀ᶠ n in atTop, (hR (ξs n)).1 ∈ K := by
      filter_upwards [hupper] with n hup
      have hlow := hlower n
      have hsecondLow : b.1.2 ≤ (hR (ξs n)).1.2 :=
        second_coord_le_of_first_coord_le g hhom (hR (ξs n)) b hup
      have hsecondUp : (hR (ξs n)).1.2 ≤ a.1.2 :=
        second_coord_le_of_first_coord_le g hhom a (hR (ξs n)) hlow
      exact ⟨⟨hlow, hsecondLow⟩, ⟨hup, hsecondUp⟩⟩
    apply support_tilt_tendsto_of_compact_unique_limit g hgcont ξs
      (fun n => hR (ξs n)) ξ a hlim (fun n => (hExtreme (ξs n)).2.1)
      K hK hmem
    intro p hp hsupportP
    let k : SupportTilt g := ⟨p, ⟨ξ, hsupportP⟩⟩
    have hak : a.1.1 ≤ k.1.1 := hp.1.1
    have hka : k.1.1 ≤ a.1.1 := ((hExtreme ξ).2.2 k hsupportP).2
    have hakEq : a = k :=
      (supportTilt_coordinate_order g hhom a k).2 (le_antisymm hak hka)
    exact (congrArg Subtype.val hakEq).symm
  · have heq (n : ℕ) : ξs n = ξ := by
      apply interiorDirection_eq_of_first_coord
      exact le_antisymm (le_of_not_gt (not_exists.mp hex n)) (hside n)
    have hf : (fun n => hR (ξs n)) = fun _ => hR ξ := by
      funext n
      rw [heq n]
    rw [hf]
    exact tendsto_const_nhds

end LPP.Busemann
