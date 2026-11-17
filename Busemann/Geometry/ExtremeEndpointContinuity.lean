/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.SupportFacesUnion
public import Busemann.Geometry.ExtremeTiltContinuity
import Busemann.Geometry.StrictSupportFaceSeparation
import Busemann.Geometry.SupportIdentities
import Busemann.Geometry.SupportOrder
import Mathlib.Tactic

/-! One-sided continuity of the literal two-face endpoints, without idempotence. -/

@[expose] public section

open Filter LPPDifferentiability
open scoped NNReal Topology

namespace LPP.Busemann

private theorem direction_eq (ξ η : InteriorDirection) (h : ξ.1.1 = η.1.1) : ξ = η := by
  apply Subtype.ext
  apply Prod.ext
  · exact h
  · apply NNReal.coe_injective
    have hc := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    linarith only [ξ.2.2.2, η.2.2.2, hc]

private theorem union_right_face
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hL hR : InteriorDirection → SupportTilt g)
    (hExtreme : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1)
    (ξ η : InteriorDirection) (hmem : η ∈ supportFacesUnion g (hL ξ) (hR ξ))
    (hside : ξ.1.1 ≤ η.1.1) : SupportsAt g η (hR ξ).1 := by
  rcases eq_or_lt_of_le hside with heq | hlt
  · have hdir := direction_eq ξ η heq
    rw [← hdir]
    exact (hExtreme ξ).2.1
  · rcases hmem with hmem | hmem
    · have hRL := support_first_coord_le_of_direction_lt g hhom ξ η (hR ξ) (hL ξ)
        (by exact_mod_cast hlt) (hExtreme ξ).2.1 hmem
      have hLR := ((hExtreme ξ).2.2 (hL ξ) (hExtreme ξ).1).2
      have heq := (supportTilt_coordinate_order g hhom (hL ξ) (hR ξ)).2
        (le_antisymm hLR hRL)
      rw [← heq]
      exact hmem
    · exact hmem

private theorem union_left_face
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hL hR : InteriorDirection → SupportTilt g)
    (hExtreme : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1)
    (ξ η : InteriorDirection) (hmem : η ∈ supportFacesUnion g (hL ξ) (hR ξ))
    (hside : η.1.1 ≤ ξ.1.1) : SupportsAt g η (hL ξ).1 := by
  rcases eq_or_lt_of_le hside with heq | hlt
  · have hdir := direction_eq η ξ heq
    rw [hdir]
    exact (hExtreme ξ).1
  · rcases hmem with hmem | hmem
    · exact hmem
    · have hRL := support_first_coord_le_of_direction_lt g hhom η ξ (hR ξ) (hL ξ)
        (by exact_mod_cast hlt) hmem (hExtreme ξ).1
      have hLR := ((hExtreme ξ).2.2 (hL ξ) (hExtreme ξ).1).2
      have heq := (supportTilt_coordinate_order g hhom (hL ξ) (hR ξ)).2
        (le_antisymm hLR hRL)
      rw [heq]
      exact hmem

private theorem endpoint_faces
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hL hR : InteriorDirection → SupportTilt g)
    (leftEndpoint rightEndpoint : InteriorDirection → InteriorDirection)
    (hExtreme : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1)
    (hInterval : ∀ ξ η : InteriorDirection,
      η ∈ supportFacesUnion g (hL ξ) (hR ξ) ↔
        (leftEndpoint ξ).1.1 ≤ η.1.1 ∧ η.1.1 ≤ (rightEndpoint ξ).1.1)
    (ξ : InteriorDirection) :
    SupportsAt g (leftEndpoint ξ) (hL ξ).1 ∧
      SupportsAt g (rightEndpoint ξ) (hR ξ).1 ∧
      (leftEndpoint ξ).1.1 ≤ ξ.1.1 ∧ ξ.1.1 ≤ (rightEndpoint ξ).1.1 := by
  have hb := (hInterval ξ ξ).mp (Or.inl (hExtreme ξ).1)
  have hLR := hb.1.trans hb.2
  have hleft := (hInterval ξ (leftEndpoint ξ)).mpr ⟨le_rfl, hLR⟩
  have hright := (hInterval ξ (rightEndpoint ξ)).mpr ⟨hLR, le_rfl⟩
  exact ⟨union_left_face g hhom hL hR hExtreme ξ (leftEndpoint ξ) hleft hb.1,
    union_right_face g hhom hL hR hExtreme ξ (rightEndpoint ξ) hright hb.2, hb⟩

/-- Both literal two-face endpoints are nondecreasing in the first direction
coordinate. Overlapping faces are compared using their actual supporting tilts;
the weak order also retains junctions of adjacent flat pieces. -/
theorem extreme_endpoints_mono
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hL hR : InteriorDirection → SupportTilt g)
    (leftEndpoint rightEndpoint : InteriorDirection → InteriorDirection)
    (hExtreme : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1)
    (hInterval : ∀ ξ η : InteriorDirection,
      η ∈ supportFacesUnion g (hL ξ) (hR ξ) ↔
        (leftEndpoint ξ).1.1 ≤ η.1.1 ∧ η.1.1 ≤ (rightEndpoint ξ).1.1)
    (ξ η : InteriorDirection) (hside : ξ.1.1 ≤ η.1.1) :
    (leftEndpoint ξ).1.1 ≤ (leftEndpoint η).1.1 ∧
      (rightEndpoint ξ).1.1 ≤ (rightEndpoint η).1.1 := by
  rcases eq_or_lt_of_le hside with heq | hlt
  · have hdir := direction_eq ξ η heq
    subst η
    exact ⟨le_rfl, le_rfl⟩
  have hltR : (ξ.1.1 : ℝ) < (η.1.1 : ℝ) := by exact_mod_cast hlt
  have hξ := endpoint_faces g hhom hL hR leftEndpoint rightEndpoint hExtreme hInterval ξ
  have hη := endpoint_faces g hhom hL hR leftEndpoint rightEndpoint hExtreme hInterval η
  constructor
  · by_cases hinside : (leftEndpoint η).1.1 < ξ.1.1
    · have hab := support_first_coord_le_of_direction_lt g hhom (leftEndpoint η) ξ
        (hL η) (hL ξ) (by exact_mod_cast hinside) hη.1 (hExtreme ξ).1
      have hba := support_first_coord_le_of_direction_lt g hhom ξ η
        (hL ξ) (hL η) hltR (hExtreme ξ).1 (hExtreme η).1
      have htilt := (supportTilt_coordinate_order g hhom (hL η) (hL ξ)).2
        (le_antisymm hab hba)
      have hcontact : SupportsAt g (leftEndpoint η) (hL ξ).1 := by
        rw [← htilt]
        exact hη.1
      exact ((hInterval ξ (leftEndpoint η)).mp (Or.inl hcontact)).1
    · exact hξ.2.2.1.trans (le_of_not_gt hinside)
  · by_cases hinside : η.1.1 < (rightEndpoint ξ).1.1
    · have hab := support_first_coord_le_of_direction_lt g hhom ξ η
        (hR ξ) (hR η) hltR (hExtreme ξ).2.1 (hExtreme η).2.1
      have hba := support_first_coord_le_of_direction_lt g hhom η (rightEndpoint ξ)
        (hR η) (hR ξ) (by exact_mod_cast hinside) (hExtreme η).2.1 hξ.2.1
      have htilt := (supportTilt_coordinate_order g hhom (hR ξ) (hR η)).2
        (le_antisymm hab hba)
      have hcontact : SupportsAt g (rightEndpoint ξ) (hR η).1 := by
        rw [← htilt]
        exact hξ.2.1
      exact ((hInterval η (rightEndpoint ξ)).mp (Or.inr hcontact)).2
    · exact (le_of_not_gt hinside).trans hη.2.2.2

private theorem support_of_frequent_tilt_limit
    (g : Quadrant → ℝ) (η : InteriorDirection)
    (hs : ℕ → SupportTilt g) (h : SupportTilt g)
    (hlim : Tendsto hs atTop (𝓝 h))
    (hcontact : ∃ᶠ n in atTop, SupportsAt g η (hs n).1) : SupportsAt g η h.1 := by
  intro z
  let F : SupportTilt g → ℝ := fun k =>
    (-k.1.1) * ((η.1.1 : ℝ) - (z.1 : ℝ)) +
      (-k.1.2) * ((η.1.2 : ℝ) - (z.2 : ℝ))
  have hF : Continuous F := by dsimp [F]; fun_prop
  exact le_of_tendsto_of_frequently ((hF.tendsto h).comp hlim)
    (hcontact.mono (fun n hn => hn z))

private theorem direction_tendsto_of_first
    (ξs : ℕ → InteriorDirection) (ξ : InteriorDirection)
    (hfirst : Tendsto (fun n => ((ξs n).1.1 : ℝ)) atTop (𝓝 (ξ.1.1 : ℝ))) :
    Tendsto ξs atTop (𝓝 ξ) := by
  have hsecondEq (n : ℕ) : ((ξs n).1.2 : ℝ) = 1 - ((ξs n).1.1 : ℝ) := by
    linarith only [(ξs n).2.2.2]
  have htarget : 1 - (ξ.1.1 : ℝ) = (ξ.1.2 : ℝ) := by linarith only [ξ.2.2.2]
  have hsecond : Tendsto (fun n => ((ξs n).1.2 : ℝ)) atTop (𝓝 (ξ.1.2 : ℝ)) := by
    simpa only [← hsecondEq, htarget] using (tendsto_const_nhds (x := (1 : ℝ))).sub hfirst
  have hfirstN : Tendsto (fun n => (ξs n).1.1) atTop (𝓝 ξ.1.1) :=
    NNReal.tendsto_coe.mp hfirst
  have hsecondN : Tendsto (fun n => (ξs n).1.2) atTop (𝓝 ξ.1.2) :=
    NNReal.tendsto_coe.mp hsecond
  apply tendsto_subtype_rng.mpr
  exact hfirstN.prodMk_nhds hsecondN

/-- The literal right endpoint is continuous under approach from the right.
This is the two-face endpoint regularity used in the outward limit argument of
GRS arXiv:1510.00860v2, (2.6)–(2.8), with junctions retained. -/
theorem tendsto_rightEndpoint_of_tendsto_from_right
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hL hR : InteriorDirection → SupportTilt g)
    (leftEndpoint rightEndpoint : InteriorDirection → InteriorDirection)
    (hExtreme : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1)
    (hInterval : ∀ ξ η : InteriorDirection,
      η ∈ supportFacesUnion g (hL ξ) (hR ξ) ↔
        (leftEndpoint ξ).1.1 ≤ η.1.1 ∧ η.1.1 ≤ (rightEndpoint ξ).1.1)
    (ξ : InteriorDirection) (ξs : ℕ → InteriorDirection)
    (hlim : Tendsto ξs atTop (𝓝 ξ))
    (hside : ∀ n : ℕ, ξ.1.1 ≤ (ξs n).1.1) :
    Tendsto (fun n => rightEndpoint (ξs n)) atTop (𝓝 (rightEndpoint ξ)) := by
  have hξ := endpoint_faces g hhom hL hR leftEndpoint rightEndpoint hExtreme hInterval ξ
  have horder := extreme_endpoints_mono g hhom hL hR leftEndpoint rightEndpoint hExtreme hInterval
  have htilt := extreme_right_tilt_tendsto_of_tendsto_from_right
    g hgcont hconc hhom hL hR hExtreme ξ ξs (fun n => by exact_mod_cast hside n) hlim
  have hcoord : Continuous (fun ζ : InteriorDirection => (ζ.1.1 : ℝ)) := by fun_prop
  have hfirst := (hcoord.tendsto ξ).comp hlim
  apply direction_tendsto_of_first
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (by exact_mod_cast (horder ξ (ξs n) (hside n)).2))
  · intro b hb
    by_cases hbOne : 1 ≤ b
    · apply Eventually.of_forall
      intro n
      have hs := (rightEndpoint (ξs n)).2.2.2
      have hpos : (0 : ℝ) < ((rightEndpoint (ξs n)).1.2 : ℝ) :=
        NNReal.coe_pos.mpr (rightEndpoint (ξs n)).2.2.1
      linarith only [hs, hpos, hbOne]
    have hbLt : b < 1 := lt_of_not_ge hbOne
    let t : ℝ := ((rightEndpoint ξ).1.1 + b) / 2
    have htLow : ((rightEndpoint ξ).1.1 : ℝ) < t := by dsimp [t]; linarith only [hb]
    have htHigh : t < b := by dsimp [t]; linarith only [hb]
    have ht0 : 0 < t := lt_trans (NNReal.coe_pos.mpr (rightEndpoint ξ).2.1) htLow
    have ht1 : t < 1 := htHigh.trans hbLt
    let η : InteriorDirection := ⟨(Real.toNNReal t, Real.toNNReal (1 - t)),
      ⟨Real.toNNReal_pos.mpr ht0, Real.toNNReal_pos.mpr (sub_pos.mpr ht1), by
        rw [Real.coe_toNNReal _ ht0.le, Real.coe_toNNReal _ (sub_nonneg.mpr ht1.le)]
        ring⟩⟩
    have hη : (η.1.1 : ℝ) = t := Real.coe_toNNReal _ ht0.le
    have hbase : (ξ.1.1 : ℝ) < t := by
      have hb := hξ.2.2.2
      have hbR : (ξ.1.1 : ℝ) ≤ ((rightEndpoint ξ).1.1 : ℝ) := by exact_mod_cast hb
      linarith only [hbR, htLow]
    have hnear : ∀ᶠ n in atTop, ((ξs n).1.1 : ℝ) < t :=
      hfirst.eventually (Iio_mem_nhds hbase)
    by_contra hnot
    have hbad : ∃ᶠ n in atTop, b ≤ ((rightEndpoint (ξs n)).1.1 : ℝ) := by
      simpa only [not_lt] using Filter.not_eventually.mp hnot
    have hcontacts : ∃ᶠ n in atTop, SupportsAt g η (hR (ξs n)).1 := by
      apply (hbad.and_eventually hnear).mono
      intro n hn
      have hs := endpoint_faces g hhom hL hR leftEndpoint rightEndpoint hExtreme hInterval (ξs n)
      have hsideη : (ξs n).1.1 ≤ η.1.1 := by
        apply NNReal.coe_le_coe.mp
        rw [hη]
        exact hn.2.le
      have hmem : η ∈ supportFacesUnion g (hL (ξs n)) (hR (ξs n)) := by
        apply (hInterval (ξs n) η).mpr
        refine ⟨hs.2.2.1.trans hsideη, ?_⟩
        apply NNReal.coe_le_coe.mp
        rw [hη]
        exact htHigh.le.trans hn.1
      exact union_right_face g hhom hL hR hExtreme (ξs n) η hmem hsideη
    have hcontact := support_of_frequent_tilt_limit g η (fun n => hR (ξs n)) (hR ξ) htilt hcontacts
    have hbound := ((hInterval ξ η).mp (Or.inr hcontact)).2
    have hboundR : (η.1.1 : ℝ) ≤ ((rightEndpoint ξ).1.1 : ℝ) := by exact_mod_cast hbound
    rw [hη] at hboundR
    linarith only [hboundR, htLow]


/-- The literal left endpoint is continuous under approach from the left.
This is the reflected two-face endpoint regularity used in the outward limit
argument of GRS arXiv:1510.00860v2, (2.6)–(2.8). -/
theorem tendsto_leftEndpoint_of_tendsto_from_left
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hL hR : InteriorDirection → SupportTilt g)
    (leftEndpoint rightEndpoint : InteriorDirection → InteriorDirection)
    (hExtreme : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1)
    (hInterval : ∀ ξ η : InteriorDirection,
      η ∈ supportFacesUnion g (hL ξ) (hR ξ) ↔
        (leftEndpoint ξ).1.1 ≤ η.1.1 ∧ η.1.1 ≤ (rightEndpoint ξ).1.1)
    (ξ : InteriorDirection) (ξs : ℕ → InteriorDirection)
    (hlim : Tendsto ξs atTop (𝓝 ξ))
    (hside : ∀ n : ℕ, (ξs n).1.1 ≤ ξ.1.1) :
    Tendsto (fun n => leftEndpoint (ξs n)) atTop (𝓝 (leftEndpoint ξ)) := by
  have hξ := endpoint_faces g hhom hL hR leftEndpoint rightEndpoint hExtreme hInterval ξ
  have horder := extreme_endpoints_mono g hhom hL hR leftEndpoint rightEndpoint hExtreme hInterval
  have htilt := extreme_left_tilt_tendsto_of_tendsto_from_left
    g hgcont hconc hhom hL hR hExtreme ξ ξs (fun n => by exact_mod_cast hside n) hlim
  have hcoord : Continuous (fun ζ : InteriorDirection => (ζ.1.1 : ℝ)) := by fun_prop
  have hfirst := (hcoord.tendsto ξ).comp hlim
  apply direction_tendsto_of_first
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases haZero : a ≤ 0
    · apply Eventually.of_forall
      intro n
      exact lt_of_le_of_lt haZero (NNReal.coe_pos.mpr (leftEndpoint (ξs n)).2.1)
    have haPos : 0 < a := lt_of_not_ge haZero
    let t : ℝ := (a + (leftEndpoint ξ).1.1) / 2
    have htLow : a < t := by dsimp [t]; linarith only [ha]
    have htHigh : t < ((leftEndpoint ξ).1.1 : ℝ) := by dsimp [t]; linarith only [ha]
    have ht0 : 0 < t := haPos.trans htLow
    have ht1 : t < 1 := by
      have hs := (leftEndpoint ξ).2.2.2
      have hpos : (0 : ℝ) < ((leftEndpoint ξ).1.2 : ℝ) :=
        NNReal.coe_pos.mpr (leftEndpoint ξ).2.2.1
      linarith only [htHigh, hs, hpos]
    let η : InteriorDirection := ⟨(Real.toNNReal t, Real.toNNReal (1 - t)),
      ⟨Real.toNNReal_pos.mpr ht0, Real.toNNReal_pos.mpr (sub_pos.mpr ht1), by
        rw [Real.coe_toNNReal _ ht0.le, Real.coe_toNNReal _ (sub_nonneg.mpr ht1.le)]
        ring⟩⟩
    have hη : (η.1.1 : ℝ) = t := Real.coe_toNNReal _ ht0.le
    have hbase : t < (ξ.1.1 : ℝ) := by
      have hb := hξ.2.2.1
      have hbR : ((leftEndpoint ξ).1.1 : ℝ) ≤ (ξ.1.1 : ℝ) := by exact_mod_cast hb
      linarith only [hbR, htHigh]
    have hnear : ∀ᶠ n in atTop, t < ((ξs n).1.1 : ℝ) :=
      hfirst.eventually (Ioi_mem_nhds hbase)
    by_contra hnot
    have hbad : ∃ᶠ n in atTop, ((leftEndpoint (ξs n)).1.1 : ℝ) ≤ a := by
      simpa only [not_lt] using Filter.not_eventually.mp hnot
    have hcontacts : ∃ᶠ n in atTop, SupportsAt g η (hL (ξs n)).1 := by
      apply (hbad.and_eventually hnear).mono
      intro n hn
      have hs := endpoint_faces g hhom hL hR leftEndpoint rightEndpoint hExtreme hInterval (ξs n)
      have hsideη : η.1.1 ≤ (ξs n).1.1 := by
        apply NNReal.coe_le_coe.mp
        rw [hη]
        exact hn.2.le
      have hmem : η ∈ supportFacesUnion g (hL (ξs n)) (hR (ξs n)) := by
        apply (hInterval (ξs n) η).mpr
        refine ⟨?_, hsideη.trans hs.2.2.2⟩
        apply NNReal.coe_le_coe.mp
        rw [hη]
        exact hn.1.trans htLow.le
      exact union_left_face g hhom hL hR hExtreme (ξs n) η hmem hsideη
    have hcontact := support_of_frequent_tilt_limit g η (fun n => hL (ξs n)) (hL ξ) htilt hcontacts
    have hbound := ((hInterval ξ η).mp (Or.inl hcontact)).1
    have hboundR : ((leftEndpoint ξ).1.1 : ℝ) ≤ (η.1.1 : ℝ) := by exact_mod_cast hbound
    rw [hη] at hboundR
    linarith only [hboundR, htHigh]
  · intro b hb
    exact Eventually.of_forall (fun n => (show ((leftEndpoint (ξs n)).1.1 : ℝ) ≤ ((leftEndpoint ξ).1.1 : ℝ) by
      exact_mod_cast (horder (ξs n) ξ (hside n)).1).trans_lt hb)


end LPP.Busemann
