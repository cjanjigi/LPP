/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.SupportFace
import Busemann.Geometry.SupportIdentities
import Busemann.Geometry.ExtremeCoordinateTilts
import LPP_Foundations.Analysis.ShapeSupportingFunctionals
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-! The two restricted stationary passage profiles outside one contact face.
This is the deterministic comparison in GRS arXiv:1510.00859v2, Lemma 6.5. -/

@[expose] public section

open LPPDifferentiability
open Filter Set
open scoped NNReal Topology

namespace LPP.Busemann

private theorem support_coordinates_straddle
    (t l α β p q gt : ℝ) (ht0 : 0 ≤ t) (htl : t < l) (hl1 : l < 1)
    (hgap : gt < α*t + β*(1-t))
    (htouch : gt = p*t + q*(1-t))
    (hlower : α*l + β*(1-l) ≤ p*l + q*(1-l)) :
    α < p ∧ q < β := by
  let dt : ℝ := (p-α)*t + (q-β)*(1-t)
  let dl : ℝ := (p-α)*l + (q-β)*(1-l)
  let d : ℝ := (p-α) - (q-β)
  have hdt : dt < 0 := by dsimp [dt]; linarith only [hgap, htouch]
  have hdl : 0 ≤ dl := by dsimp [dl]; linarith only [hlower]
  have hfactor : (l-t)*d = dl-dt := by dsimp [d, dl, dt]; ring
  have hprod : 0 < (l-t)*d := by rw [hfactor]; linarith only [hdl, hdt]
  have hd : 0 < d := by
    by_contra hnot
    have hnonpos : (l-t)*d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr htl.le) (le_of_not_gt hnot)
    linarith only [hnonpos, hprod]
  have hp : p-α = dl+(1-l)*d := by dsimp [dl, d]; ring
  have hq : q-β = dt-t*d := by dsimp [dt, d]; ring
  have hpositive : 0 < (1-l)*d := mul_pos (sub_pos.mpr hl1) hd
  have hnonnegative : 0 ≤ t*d := mul_nonneg ht0 hd.le
  constructor
  · linarith only [hp, hdl, hpositive]
  · linarith only [hq, hdt, hnonnegative]

private theorem left_profile_comparison
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hconc : ∀ (a b : Quadrant) (c d : ℝ≥0), c + d = 1 →
      (c : ℝ) * g a + (d : ℝ) * g b ≤ g (c • a + d • b))
    (α β : ℝ)
    (hmajorant : ∀ z : Quadrant,
      g z ≤ α * (z.1 : ℝ) + β * (z.2 : ℝ))
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (hcontactL : g (Real.toNNReal l, Real.toNNReal (1-l)) = α*l + β*(1-l))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htl : t < l)
    (hstrict : g (Real.toNNReal t, Real.toNNReal (1-t)) < α*t + β*(1-t)) :
    let H : ℝ := sSup ((fun u : ℝ =>
      g (Real.toNNReal (t-u), Real.toNNReal (1-t)) + α*u) '' Set.Icc 0 t)
    let V : ℝ := sSup ((fun u : ℝ =>
      g (Real.toNNReal t, Real.toNNReal (1-t-u)) + β*u) '' Set.Icc 0 (1-t))
    H = g (Real.toNNReal t, Real.toNNReal (1-t)) ∧
      V = α*t + β*(1-t) ∧ H < V := by
  let q : Quadrant := (Real.toNNReal t, Real.toNNReal (1-t))
  let L : ℝ := α*t + β*(1-t)
  let fH : ℝ → ℝ := fun u =>
    g (Real.toNNReal (t-u), Real.toNNReal (1-t)) + α*u
  let fV : ℝ → ℝ := fun u =>
    g (Real.toNNReal t, Real.toNNReal (1-t-u)) + β*u
  let SH : Set ℝ := fH '' Set.Icc 0 t
  let SV : Set ℝ := fV '' Set.Icc 0 (1-t)
  change sSup SH = g q ∧ sSup SV = L ∧ sSup SH < sSup SV
  have hOneMinusT : 0 ≤ 1-t := by linarith
  have hOneMinusL : 0 < 1-l := by linarith
  have hscale (c : ℝ) (hc : 0 ≤ c) :
      g (Real.toNNReal (c*l), Real.toNNReal (c*(1-l))) =
        α*(c*l) + β*(c*(1-l)) := by
    let cn : ℝ≥0 := Real.toNNReal c
    have hcoords : cn • (Real.toNNReal l, Real.toNNReal (1-l)) =
        (Real.toNNReal (c*l), Real.toNNReal (c*(1-l))) := by
      apply Prod.ext <;> apply NNReal.coe_injective
      · change (cn : ℝ) * (Real.toNNReal l : ℝ) =
          (Real.toNNReal (c*l) : ℝ)
        rw [Real.coe_toNNReal _ hc, Real.coe_toNNReal _ hl0.le,
          Real.coe_toNNReal _ (mul_nonneg hc hl0.le)]
      · change (cn : ℝ) * (Real.toNNReal (1-l) : ℝ) =
          (Real.toNNReal (c*(1-l)) : ℝ)
        rw [Real.coe_toNNReal _ hc, Real.coe_toNNReal _ hOneMinusL.le,
          Real.coe_toNNReal _ (mul_nonneg hc hOneMinusL.le)]
    rw [← hcoords, hhom, hcontactL, Real.coe_toNNReal _ hc]
    ring
  -- Both profile sets contain the zero exit and lie below the support plane.
  have hSHnonempty : SH.Nonempty := by
    refine ⟨fH 0, ⟨0, ⟨le_refl 0, ht0⟩, rfl⟩⟩
  have hSVnonempty : SV.Nonempty := by
    refine ⟨fV 0, ⟨0, ⟨le_refl 0, hOneMinusT⟩, rfl⟩⟩
  have hSHupper : ∀ y ∈ SH, y ≤ L := by
    rintro y ⟨u, hu, rfl⟩
    have htu : 0 ≤ t-u := by linarith [hu.2]
    have hsecond : (Real.toNNReal (1-t) : ℝ) = 1-t :=
      Real.coe_toNNReal _ hOneMinusT
    have hfirst : (Real.toNNReal (t-u) : ℝ) = t-u :=
      Real.coe_toNNReal _ htu
    have hm := hmajorant (Real.toNNReal (t-u), Real.toNNReal (1-t))
    rw [hfirst, hsecond] at hm
    dsimp [fH, L]
    linarith
  have hSVupper : ∀ y ∈ SV, y ≤ L := by
    rintro y ⟨u, hu, rfl⟩
    have htu : 0 ≤ 1-t-u := by linarith [hu.2]
    have hfirst : (Real.toNNReal t : ℝ) = t := Real.coe_toNNReal _ ht0
    have hsecond : (Real.toNNReal (1-t-u) : ℝ) = 1-t-u :=
      Real.coe_toNNReal _ htu
    have hm := hmajorant (Real.toNNReal t, Real.toNNReal (1-t-u))
    rw [hfirst, hsecond] at hm
    dsimp [fV, L]
    linarith
  have hSHbdd : BddAbove SH := ⟨L, hSHupper⟩
  have hSVbdd : BddAbove SV := ⟨L, hSVupper⟩
  have hSVle : sSup SV ≤ L := csSup_le hSVnonempty hSVupper
  -- A scaled contact point attains the winning vertical profile.
  let cV : ℝ := t/l
  let b : ℝ := cV*(1-l)
  let uV : ℝ := 1-t-b
  have hcV : 0 ≤ cV := div_nonneg ht0 hl0.le
  have htcV : cV*l = t := by dsimp [cV]; field_simp [ne_of_gt hl0]
  have hb0 : 0 ≤ b := mul_nonneg hcV hOneMinusL.le
  have hbLe : b ≤ 1-t := by
    have hbmul : b*l ≤ (1-t)*l := by
      calc
        b*l = (cV*l)*(1-l) := by dsimp [b]; ring
        _ = t*(1-l) := by rw [htcV]
        _ ≤ (1-t)*l := by nlinarith only [htl]
    exact le_of_mul_le_mul_right hbmul hl0
  have huV : uV ∈ Set.Icc 0 (1-t) := by dsimp [uV]; constructor <;> linarith
  have hwinV : fV uV = L := by
    have hscaleV := hscale cV hcV
    have hsecond : 1-t-uV = cV*(1-l) := by dsimp [uV, b]; ring
    have hfirst : Real.toNNReal t = Real.toNNReal (cV*l) := by rw [htcV]
    dsimp [fV, L]
    rw [hfirst, hsecond, hscaleV]
    rw [htcV]
    dsimp [uV, b]
    ring
  have hSVge : L ≤ sSup SV := le_csSup hSVbdd ⟨uV, huV, hwinV⟩
  have hVequal : sSup SV = L := le_antisymm hSVle hSVge
  have hSHge : g q ≤ sSup SH := by
    have hmem : fH 0 ∈ SH := ⟨0, ⟨le_refl 0, ht0⟩, rfl⟩
    have hval : fH 0 = g q := by simp [fH, q]
    rw [← hval]
    exact le_csSup hSHbdd hmem
  -- On the axis the losing exit set is a singleton. In the interior the
  -- coordinate derivatives give the source tangent and small-exit arguments.
  have hcomparison : sSup SH = g q ∧ g q < sSup SV := by
    by_cases htZero : t = 0
    · have hSHle : sSup SH ≤ g q := by
        apply csSup_le hSHnonempty
        rintro y ⟨u, hu, rfl⟩
        have hu0 : u = 0 := by rcases hu with ⟨hlo, hhi⟩; linarith only [hlo, hhi, htZero]
        subst u
        simp only [fH, q, sub_zero, mul_zero, add_zero, le_refl]
      exact ⟨le_antisymm hSHle hSHge, by rw [hVequal]; exact hstrict⟩
    · have htPos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htZero)
      have htLtOne : t < 1 := lt_trans htl hl1
      let ξ : InteriorDirection :=
        ⟨(Real.toNNReal t, Real.toNNReal (1-t)),
          ⟨Real.toNNReal_pos.mpr htPos,
            Real.toNNReal_pos.mpr (sub_pos.mpr htLtOne), by
              rw [Real.coe_toNNReal t ht0,
                Real.coe_toNNReal (1-t) hOneMinusT]
              ring⟩⟩
      have hξFirst : (ξ.1.1 : ℝ) = t := Real.coe_toNNReal t ht0
      have hξSecond : (ξ.1.2 : ℝ) = 1-t :=
        Real.coe_toNNReal (1-t) hOneMinusT
      let a : ℝ := (ξ.1.1 : ℝ)
      let U1 : ℝ → ℝ := fun s => quadrantExtension g (a+s, 1-a)
      let U2 : ℝ → ℝ := fun s => quadrantExtension g (a, 1-a+s)
      let kL : ℝ × ℝ :=
        (-derivWithin U1 (Iio 0) 0, -derivWithin U2 (Ioi 0) 0)
      let kR : ℝ × ℝ :=
        (-derivWithin U1 (Ioi 0) 0, -derivWithin U2 (Iio 0) 0)
      have hcanonical := coordinate_extreme_tilts_support_and_order g hconc hhom ξ
      change SupportsAt g ξ kL ∧ SupportsAt g ξ kR ∧
        (∀ k : ℝ × ℝ, SupportsAt g ξ k → kL.1 ≤ k.1 ∧ k.1 ≤ kR.1)
        at hcanonical
      have hcoordinates (k : ℝ × ℝ) (hk : SupportsAt g ξ k) :
          α < -k.1 ∧ -k.2 < β := by
        have hs := (supportsAt_iff_through_origin_majorant_and_contact
          g ξ k hhom).mp hk
        have htouched : g q = (-k.1)*t + (-k.2)*(1-t) := by
          simpa only [hξFirst, hξSecond] using hs.2
        have hbounded : α*l+β*(1-l) ≤ (-k.1)*l+(-k.2)*(1-l) := by
          have hm := hs.1 (Real.toNNReal l, Real.toNNReal (1-l))
          rw [Real.coe_toNNReal _ hl0.le,
            Real.coe_toNNReal _ hOneMinusL.le] at hm
          linarith only [hm, hcontactL]
        exact support_coordinates_straddle t l α β (-k.1) (-k.2)
          (g q) ht0 htl hl1 hstrict htouched hbounded
      have hpL : α < -kL.1 := (hcoordinates kL hcanonical.1).1
      have hqR : -kR.2 < β := (hcoordinates kR hcanonical.2.1).2
      have hleftTouch : g q = (-kL.1)*t + (-kL.2)*(1-t) := by
        have hs := (supportsAt_iff_through_origin_majorant_and_contact
          g ξ kL hhom).mp hcanonical.1
        simpa only [hξFirst, hξSecond] using hs.2
      -- The first left coordinate derivative is the tangent slope. Concavity
      -- bounds every horizontal exit by its zero-exit value.
      have hSHle : sSup SH ≤ g q := by
        apply csSup_le hSHnonempty
        rintro y ⟨u, hu, rfl⟩
        have htu : 0 ≤ t-u := by linarith only [hu.2]
        have hm := ((supportsAt_iff_through_origin_majorant_and_contact
          g ξ kL hhom).mp hcanonical.1).1
          (Real.toNNReal (t-u), Real.toNNReal (1-t))
        rw [Real.coe_toNNReal _ htu,
          Real.coe_toNNReal _ hOneMinusT] at hm
        have hgain : 0 ≤ (-kL.1-α)*u :=
          mul_nonneg (sub_nonneg.mpr hpL.le) hu.1
        change fH u ≤ g q
        dsimp only [fH]
        linarith only [hm, hleftTouch, hgain]
      have hHequal : sSup SH = g q := le_antisymm hSHle hSHge
      -- The second left coordinate derivative is below beta. Its negative
      -- displacement therefore gives an actual small positive vertical exit.
      have hU2 : U2 = (fun s : ℝ => quadrantExtension g (t, 1-t+s)) := by
        funext s
        simp only [U2, a, hξFirst]
      have hderiv0 := hasDerivWithinAt_second_coordinate_left
        g hconc hhom t htPos htLtOne
      rw [← hU2] at hderiv0
      have hderiv : HasDerivWithinAt U2
          (derivWithin U2 (Iio 0) 0) (Iio 0) 0 := by
        rw [hderiv0.derivWithin (uniqueDiffWithinAt_Iio 0)]
        exact hderiv0
      have hqRderiv : derivWithin U2 (Iio 0) 0 < β := by
        simpa only [kR, neg_neg] using hqR
      have hlimit : Tendsto (slope U2 0) (𝓝[<] (0 : ℝ))
          (𝓝 (derivWithin U2 (Iio 0) 0)) :=
        (hasDerivWithinAt_iff_tendsto_slope'
          (by simp only [mem_Iio, lt_self_iff_false, not_false_eq_true])).1 hderiv
      have hslopes : ∀ᶠ s : ℝ in 𝓝[<] 0, slope U2 0 s < β :=
        hlimit.eventually (Iio_mem_nhds hqRderiv)
      have hnear0 : Ioi (t-1) ∈ 𝓝 (0 : ℝ) :=
        Ioi_mem_nhds (by linarith only [htLtOne])
      have hnear : ∀ᶠ s : ℝ in 𝓝[<] 0, t-1 < s :=
        mem_nhdsWithin_of_mem_nhds hnear0
      obtain ⟨s, ⟨hsSlope, hsNear⟩, hsNeg⟩ :=
        ((hslopes.and hnear).and self_mem_nhdsWithin).exists
      have hslot : -s ∈ Set.Icc 0 (1-t) := by
        constructor <;> linarith only [hsNear, hsNeg]
      have hratio : β*s < U2 s - U2 0 := by
        rw [slope_def_field, sub_zero] at hsSlope
        exact (div_lt_iff_of_neg hsNeg).1 hsSlope
      have hzero : U2 0 = g q := by
        rw [hU2]
        change g (Real.toNNReal t, Real.toNNReal (1-t+0)) = g q
        simp only [add_zero, q]
      have hvalue : fV (-s) = U2 s - β*s := by
        rw [hU2]
        dsimp only [fV, quadrantExtension, toQuadrant]
        have harg : 1-t-(-s)=1-t+s := by ring
        rw [harg]
        ring
      have hsmall : g q < fV (-s) := by
        rw [hvalue]
        rw [hzero] at hratio
        linarith only [hratio]
      have hmem : fV (-s) ∈ SV := ⟨-s, hslot, rfl⟩
      exact ⟨hHequal, lt_of_lt_of_le hsmall (le_csSup hSVbdd hmem)⟩
  exact ⟨hcomparison.1, hVequal, by rw [hcomparison.1]; exact hcomparison.2⟩

/-- Outside one whole support face, the restricted boundary profile on the
near side equals the ordinary shape and the other reaches the support plane.
This is the deterministic comparison in GRS arXiv:1510.00859v2, Lemma 6.5,
with the closed axes included as an elementary extension. -/
theorem restricted_profiles_compare_outside_contact
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z)
    (hconc : ∀ (a b : Quadrant) (c d : ℝ≥0), c + d = 1 →
      (c : ℝ) * g a + (d : ℝ) * g b ≤ g (c • a + d • b))
    (h : SupportTilt g)
    (hmajorant : ∀ z : Quadrant,
      g z ≤ (-h.1.1) * (z.1 : ℝ) + (-h.1.2) * (z.2 : ℝ))
    (left right : InteriorDirection)
    (hleft : left ∈ supportFace g h)
    (hright : right ∈ supportFace g h)
    (hcontact : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      (g (Real.toNNReal t, Real.toNNReal (1 - t)) +
        h.1.1 * t + h.1.2 * (1 - t) = 0 ↔
          (left.1.1 : ℝ) ≤ t ∧ t ≤ (right.1.1 : ℝ)))
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    let H : ℝ := sSup ((fun u : ℝ =>
      g (Real.toNNReal (t - u), Real.toNNReal (1 - t)) - h.1.1 * u)
        '' Set.Icc 0 t)
    let V : ℝ := sSup ((fun u : ℝ =>
      g (Real.toNNReal t, Real.toNNReal (1 - t - u)) - h.1.2 * u)
        '' Set.Icc 0 (1 - t))
    (t < (left.1.1 : ℝ) →
      H = g (Real.toNNReal t, Real.toNNReal (1 - t)) ∧
      V = (-h.1.1) * t + (-h.1.2) * (1 - t) ∧ H < V) ∧
    ((right.1.1 : ℝ) < t →
      V = g (Real.toNNReal t, Real.toNNReal (1 - t)) ∧
      H = (-h.1.1) * t + (-h.1.2) * (1 - t) ∧ V < H) := by
  have hleftFirstPos : (0 : ℝ) < (left.1.1 : ℝ) := NNReal.coe_pos.2 left.2.1
  have hleftSecondPos : (0 : ℝ) < (left.1.2 : ℝ) := NNReal.coe_pos.2 left.2.2.1
  have hleftFirstLtOne : (left.1.1 : ℝ) < 1 := by
    have hs := left.2.2.2
    linarith
  have hrightFirstPos : (0 : ℝ) < (right.1.1 : ℝ) := NNReal.coe_pos.2 right.2.1
  have hrightSecondPos : (0 : ℝ) < (right.1.2 : ℝ) := NNReal.coe_pos.2 right.2.2.1
  have hrightFirstLtOne : (right.1.1 : ℝ) < 1 := by
    have hs := right.2.2.2
    linarith
  have hleftSupport :=
    ((supportsAt_iff_through_origin_majorant_and_contact g left h.1 hhom).mp hleft).2
  have hrightSupport :=
    ((supportsAt_iff_through_origin_majorant_and_contact g right h.1 hhom).mp hright).2
  have hleftContact :
      g (Real.toNNReal (left.1.1 : ℝ), Real.toNNReal (1-(left.1.1 : ℝ))) =
        (-h.1.1)*(left.1.1 : ℝ)+(-h.1.2)*(1-(left.1.1 : ℝ)) := by
    have hs := left.2.2.2
    have hq : (Real.toNNReal (left.1.1 : ℝ),
        Real.toNNReal (1-(left.1.1 : ℝ))) = left.1 := by
      apply Prod.ext <;> apply NNReal.coe_injective
      · rw [Real.coe_toNNReal _ hleftFirstPos.le]
      · rw [Real.coe_toNNReal _ (by linarith : 0 ≤ 1-(left.1.1 : ℝ))]
        exact_mod_cast (by linarith : (1 : ℝ)-(left.1.1 : ℝ) = (left.1.2 : ℝ))
    rw [hq]
    have hsSecond : (left.1.2 : ℝ) = 1-(left.1.1 : ℝ) := by linarith [hs]
    rw [hsSecond] at hleftSupport
    exact hleftSupport
  have hrightContact :
      g (Real.toNNReal (right.1.1 : ℝ), Real.toNNReal (1-(right.1.1 : ℝ))) =
        (-h.1.1)*(right.1.1 : ℝ)+(-h.1.2)*(1-(right.1.1 : ℝ)) := by
    have hs := right.2.2.2
    have hq : (Real.toNNReal (right.1.1 : ℝ),
        Real.toNNReal (1-(right.1.1 : ℝ))) = right.1 := by
      apply Prod.ext <;> apply NNReal.coe_injective
      · rw [Real.coe_toNNReal _ hrightFirstPos.le]
      · rw [Real.coe_toNNReal _ (by linarith : 0 ≤ 1-(right.1.1 : ℝ))]
        exact_mod_cast (by linarith : (1 : ℝ)-(right.1.1 : ℝ) = (right.1.2 : ℝ))
    rw [hq]
    have hsSecond : (right.1.2 : ℝ) = 1-(right.1.1 : ℝ) := by linarith [hs]
    rw [hsSecond] at hrightSupport
    exact hrightSupport
  have hstrict (s : ℝ) (hs : s ∈ Set.Icc 0 1)
      (hout : s < (left.1.1 : ℝ) ∨ (right.1.1 : ℝ) < s) :
      g (Real.toNNReal s, Real.toNNReal (1-s)) <
        (-h.1.1)*s+(-h.1.2)*(1-s) := by
    have hm := hmajorant (Real.toNNReal s, Real.toNNReal (1-s))
    rw [Real.coe_toNNReal _ hs.1,
      Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)] at hm
    have hne : g (Real.toNNReal s, Real.toNNReal (1-s)) +
        h.1.1*s+h.1.2*(1-s) ≠ 0 := by
      intro heq
      have hc := (hcontact s hs).mp heq
      rcases hout with hlt | hgt
      · exact (not_lt_of_ge hc.1) hlt
      · exact (not_lt_of_ge hc.2) hgt
    exact lt_of_le_of_ne hm (by intro heq; apply hne; linarith)
  constructor
  · intro htl
    simpa only [sub_eq_add_neg, neg_mul] using
      left_profile_comparison g hhom hconc (-h.1.1) (-h.1.2) hmajorant
        (left.1.1 : ℝ) hleftFirstPos hleftFirstLtOne hleftContact
        t ht.1 ht.2 htl (hstrict t ht (Or.inl htl))
  · intro hrt
    -- Coordinate exchange gives the right-side comparison on the same profiles.
    let gs : Quadrant → ℝ := fun z => g (z.2, z.1)
    have hhomS (c : ℝ≥0) (z : Quadrant) :
        gs (c • z) = (c : ℝ)*gs z := by
      change g (c • z.2, c • z.1) = (c : ℝ)*g (z.2, z.1)
      simpa only [Prod.smul_mk] using hhom c (z.2, z.1)
    have hconcS (a b : Quadrant) (c d : ℝ≥0) (hcd : c+d=1) :
        (c : ℝ)*gs a+(d : ℝ)*gs b ≤ gs (c • a+d • b) := by
      change (c : ℝ)*g (a.2,a.1)+(d : ℝ)*g (b.2,b.1) ≤
        g (c • a.2+d • b.2, c • a.1+d • b.1)
      simpa only [Prod.smul_mk, Prod.mk_add_mk] using
        hconc (a.2,a.1) (b.2,b.1) c d hcd
    have hmajorS (z : Quadrant) :
        gs z ≤ (-h.1.2)*(z.1 : ℝ)+(-h.1.1)*(z.2 : ℝ) := by
      have hm := hmajorant (z.2,z.1)
      dsimp [gs]
      linarith only [hm]
    have hswapT : 0 ≤ 1-t ∧ 1-t ≤ 1 := by constructor <;> linarith [ht.1, ht.2]
    have hswapLeft : 1-t < 1-(right.1.1 : ℝ) := by linarith
    have hcontactS :
        gs (Real.toNNReal (1-(right.1.1 : ℝ)),
            Real.toNNReal (1-(1-(right.1.1 : ℝ)))) =
          (-h.1.2)*(1-(right.1.1 : ℝ))+
            (-h.1.1)*(1-(1-(right.1.1 : ℝ))) := by
      dsimp [gs]
      convert hrightContact using 1 <;> ring_nf
    have hstrictS :
        gs (Real.toNNReal (1-t), Real.toNNReal (1-(1-t))) <
          (-h.1.2)*(1-t)+(-h.1.1)*(1-(1-t)) := by
      dsimp [gs]
      convert hstrict t ht (Or.inr hrt) using 1 <;> ring_nf
    have hs := left_profile_comparison gs hhomS hconcS
      (-h.1.2) (-h.1.1) hmajorS (1-(right.1.1 : ℝ))
      (by linarith [hrightFirstLtOne]) (by linarith [hrightFirstPos])
      hcontactS (1-t) hswapT.1 hswapT.2 hswapLeft hstrictS
    have hident : (1 : ℝ)-(1-t)=t := by ring
    simp only [gs, hident] at hs
    simpa only [sub_eq_add_neg, neg_mul, add_comm, add_left_comm,
      add_assoc] using hs

end LPP.Busemann
