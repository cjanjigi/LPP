/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.CrossingRemarks.Translation
public import Differentiability.FinalDraft.TailConsequences.FiniteSites
import LPP_Foundations.Model.Paths.HorizontalFirst
import Mathlib.Tactic

/-! A heavy vertex is a one-step witness in the actual arbitrary-endpoint
region. This gives the necessary upper-tail condition from the final
differentiability draft, Section 6 Proposition `prop:endpoints` and subsection `sub:ub_mom-chat`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace LPPDifferentiability.FinalDraft

/-- The signed lattice region in Proposition `prop:endpoints`. -/
def endpointRegion (a A R s ell : ℝ) : Set Lattice :=
  {z | |(z.1 : ℝ) + (z.2 : ℝ)| ≤ A * ell ∧ |stripTransverse a z| ≤ R * s}

/-- The literal arbitrary-endpoint event, with the two extreme supports of the
shape profile and the terminal vertex excluded from the weight. -/
def endpointFastEvent (g : Quadrant → ℝ) (a A R s ell ε : ℝ) : Set Environment :=
  {ω | ∃ (u : Lattice) (d : ℕ × ℕ) (p : Path u d),
    (∀ i, p.vertex i ∈ endpointRegion a A R s ell) ∧
      ∃ right : Bool, crossingSupport g a right d + ε * s < pathWeight ω p}

/-- The signed support formulation agrees with the minimum of the two defects
in the centered arbitrary-endpoint probability estimate. -/
theorem endpointFastEvent_eq_defect (g : Quadrant → ℝ) (a A R s ell ε : ℝ) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let dl := derivWithin H (Iio 0) 0
    let dr := derivWithin H (Ioi 0) 0
    endpointFastEvent g a A R s ell ε =
      {ω : Environment | ∃ (u : Lattice) (d : ℕ × ℕ) (p : Path u d),
        (∀ i, |((p.vertex i).1 : ℝ) + ((p.vertex i).2 : ℝ)| ≤ A * ell ∧
          |(1 - a) * ((p.vertex i).1 : ℝ) - a * ((p.vertex i).2 : ℝ)| ≤ R * s) ∧
        min (H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) +
              dl * ((1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)) - pathWeight ω p)
            (H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) +
              dr * ((1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)) - pathWeight ω p) < -(ε * s)} := by
  intro H dl dr
  ext ω
  constructor
  · rintro ⟨u, d, p, hregion, right, hfast⟩
    refine ⟨u, d, p, hregion, min_lt_iff.mpr ?_⟩
    cases right
    · left
      simp only [crossingSupport, Bool.false_eq_true, ite_false, stripTransverse, Int.cast_natCast] at hfast
      linarith only [hfast]
    · right
      simp only [crossingSupport, ite_true, stripTransverse, Int.cast_natCast] at hfast
      linarith only [hfast]
  · rintro ⟨u, d, p, hregion, hfast⟩
    refine ⟨u, d, p, hregion, ?_⟩
    rcases min_lt_iff.mp hfast with hleft | hright
    · refine ⟨false, ?_⟩
      simp only [crossingSupport, Bool.false_eq_true, ite_false, stripTransverse, Int.cast_natCast]
      linarith only [hleft]
    · refine ⟨true, ?_⟩
      simp only [crossingSupport, ite_true, stripTransverse, Int.cast_natCast]
      linarith only [hright]

private theorem exists_endpoint_start_sites (a A R s ell : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hLevel : 2 ≤ A * ell) (hWidth : 2 ≤ R * s) :
    ∃ Q : Finset Lattice, (A * R / 4) * (s * ell) ≤ (Q.card : ℝ) ∧
      ∀ z ∈ Q, z ∈ endpointRegion a A R s ell ∧
        z + ((1, 0) : Lattice) ∈ endpointRegion a A R s ell := by
  let N : ℕ := ⌊A * ell⌋₊
  let M : ℕ := ⌊R * s⌋₊
  let site : Fin N × Fin M → Lattice := fun ij =>
    let I : ℤ := ij.1.val
    let x : ℤ := ⌊a * (ij.1.val : ℝ)⌋ + (ij.2.val : ℤ)
    (x, I - x)
  have hlevel (ij : Fin N × Fin M) : (site ij).1 + (site ij).2 = (ij.1.val : ℤ) := by
    simp only [site]
    omega
  have hinj : Function.Injective site := by
    intro i j h
    have hl := congrArg (fun z : Lattice => z.1 + z.2) h
    rw [hlevel, hlevel] at hl
    have hi : i.1.val = j.1.val := by exact_mod_cast hl
    have hx := congrArg Prod.fst h
    change ⌊a * (i.1.val : ℝ)⌋ + (i.2.val : ℤ) =
      ⌊a * (j.1.val : ℝ)⌋ + (j.2.val : ℤ) at hx
    rw [hi] at hx
    exact Prod.ext (Fin.ext hi) (Fin.ext (by omega))
  let Q : Finset Lattice := Finset.univ.map ⟨site, hinj⟩
  have hNlow : A * ell / 2 ≤ (N : ℝ) := by
    dsimp only [N]
    linarith only [hLevel, Nat.lt_floor_add_one (A * ell)]
  have hMlow : R * s / 2 ≤ (M : ℝ) := by
    dsimp only [M]
    linarith only [hWidth, Nat.lt_floor_add_one (R * s)]
  have hNhigh : (N : ℝ) ≤ A * ell := Nat.floor_le (by linarith)
  have hMhigh : (M : ℝ) ≤ R * s := Nat.floor_le (by linarith)
  refine ⟨Q, ?_, ?_⟩
  · simp only [Q, Finset.card_map, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ = (A * ell / 2) * (R * s / 2) := by ring
      _ ≤ _ := mul_le_mul hNlow hMlow (by linarith) (Nat.cast_nonneg _)
  · intro z hz
    rcases Finset.mem_map.mp hz with ⟨ij, _, rfl⟩
    change site ij ∈ endpointRegion a A R s ell ∧
      site ij + ((1, 0) : Lattice) ∈ endpointRegion a A R s ell
    have hI : ((site ij).1 : ℝ) + ((site ij).2 : ℝ) = (ij.1.val : ℝ) := by
      exact_mod_cast hlevel ij
    have hi : (ij.1.val : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt ij.1.isLt)
    have hj : (ij.2.val : ℝ) + 1 ≤ (M : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt ij.2.isLt)
    have hρ : stripTransverse a (site ij) =
        (⌊a * (ij.1.val : ℝ)⌋ : ℤ) + (ij.2.val : ℝ) - a * (ij.1.val : ℝ) := by
      unfold stripTransverse
      rw [show (1 - a) * ((site ij).1 : ℝ) - a * ((site ij).2 : ℝ) =
        ((site ij).1 : ℝ) - a * (((site ij).1 : ℝ) + ((site ij).2 : ℝ)) by ring, hI]
      simp only [site, Int.cast_add, Int.cast_natCast]
    have hρlow : -1 ≤ stripTransverse a (site ij) := by
      rw [hρ]
      linarith only [Int.lt_floor_add_one (a * (ij.1.val : ℝ)), (Nat.cast_nonneg ij.2.val : 0 ≤ (ij.2.val : ℝ))]
    have hρhigh : stripTransverse a (site ij) ≤ (ij.2.val : ℝ) := by
      rw [hρ]
      linarith only [Int.floor_le (a * (ij.1.val : ℝ))]
    have hI' : (((site ij + ((1, 0) : Lattice)).1 : ℤ) : ℝ) +
        ((site ij + ((1, 0) : Lattice)).2 : ℝ) = (ij.1.val : ℝ) + 1 := by
      simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one, add_zero]
      linarith only [hI]
    have hρ' : stripTransverse a (site ij + ((1, 0) : Lattice)) =
        stripTransverse a (site ij) + (1 - a) := by
      simp only [stripTransverse, Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one,
        add_zero]
      ring
    constructor
    · refine ⟨?_, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      rw [hI, abs_of_nonneg (Nat.cast_nonneg _)]
      linarith only [hi, hNhigh]
    · refine ⟨?_, ?_⟩
      · rw [hI', abs_of_nonneg (by positivity)]
        exact hi.trans hNhigh
      · rw [hρ']
        exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem endpointFastEvent_of_site_above {ω : Environment} (g : Quadrant → ℝ)
    (a A R s ell ε : ℝ) (z : Lattice)
    (hstart : z ∈ endpointRegion a A R s ell)
    (hfinish : z + ((1, 0) : Lattice) ∈ endpointRegion a A R s ell)
    (hfast : crossingSupport g a false (1, 0) + ε * s < ω z) :
    ω ∈ endpointFastEvent g a A R s ell ε := by
  let p := horizontalFirst z (1, 0)
  have hp0 : p.vertex (0 : Fin 2) = z := p.start
  have hp1 : p.vertex (1 : Fin 2) = z + ((1, 0) : Lattice) := p.finish
  have hpweight : pathWeight ω p = ω z := by
    change (∑ i : Fin 1, ω (p.vertex i.castSucc)) = ω z
    rw [Fin.sum_univ_one]
    exact congrArg ω hp0
  refine ⟨z, (1, 0), p, ?_, false, ?_⟩
  · intro i
    fin_cases i
    · change p.vertex (0 : Fin 2) ∈ endpointRegion a A R s ell
      rw [hp0]
      exact hstart
    · change p.vertex (1 : Fin 2) ∈ endpointRegion a A R s ell
      rw [hp1]
      exact hfinish
  · rw [hpweight]
    exact hfast

/-- The upper bound of Proposition `prop:endpoints` forces the displayed
single-site upper-tail condition, along the same record set. No tail moment
assumption is needed for this implication. -/
theorem endpoint_upper_tail_tendsto_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (a A R : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hA : 0 < A) (hR : 0 < R)
    (m : ℕ → ℕ) (records : Set ℕ)
    (hell : Tendsto (fun k : ℕ => (2 : ℝ) ^ m k) (atTop ⊓ 𝓟 records) atTop)
    (hendpoint : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k : ℕ => (environmentLaw μ).real
        (endpointFastEvent g a A R ((2 : ℝ) ^ k) ((2 : ℝ) ^ m k) ε))
        (atTop ⊓ 𝓟 records) (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun k : ℕ => (2 : ℝ) ^ k * (2 : ℝ) ^ m k *
      μ.real (Ioi (δ * (2 : ℝ) ^ k))) (atTop ⊓ 𝓟 records) (𝓝 0) := by
  let F : Filter ℕ := atTop ⊓ 𝓟 records
  let s (k : ℕ) : ℝ := 2 ^ k
  let ell (k : ℕ) : ℝ := 2 ^ m k
  let c := A * R / 4
  let score := crossingSupport g a false (1, 0)
  have hc : 0 < c := by positivity
  have hs : Tendsto s F atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).mono_left inf_le_left
  have hlevels : ∀ᶠ k in F, 2 ≤ A * ell k := (hell.const_mul_atTop hA).eventually_ge_atTop 2
  have hwidth : ∀ᶠ k in F, 2 ≤ R * s k := (hs.const_mul_atTop hR).eventually_ge_atTop 2
  have hscore : ∀ᶠ k in F, score ≤ (δ / 2) * s k :=
    (hs.const_mul_atTop (half_pos hδ)).eventually_ge_atTop score
  change Tendsto (fun k => s k * ell k * μ.real (Ioi (δ * s k))) F (𝓝 0)
  rw [tendsto_order]
  constructor
  · intro x hx
    exact Eventually.of_forall fun k =>
      hx.trans_le (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _))
        measureReal_nonneg)
  · intro x hx
    have hxexp : 0 < 1 - Real.exp (-(c * x)) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      exact neg_neg_of_pos (mul_pos hc hx)
    have hrare := (tendsto_order.mp (hendpoint (δ / 2) (half_pos hδ))).2 _ hxexp
    filter_upwards [hlevels, hwidth, hscore, hrare] with k hℓ hw hf hPk
    let q := μ.real (Ioi (δ * s k))
    have hq0 : 0 ≤ q := measureReal_nonneg
    have hq1 : q ≤ 1 := measureReal_le_one
    obtain ⟨Q, hcard, hQ⟩ := exists_endpoint_start_sites a A R (s k) (ell k)
      ha₀.le ha₁.le hℓ hw
    have hsubset :
        {ω : Environment | ∃ z ∈ Q, δ * s k < ω z} ⊆ endpointFastEvent g a A R (s k) (ell k) (δ / 2) := by
      rintro ω ⟨z, hz, hω⟩
      obtain ⟨hstart, hfinish⟩ := hQ z hz
      exact endpointFastEvent_of_site_above g a A R (s k) (ell k) (δ / 2) z hstart hfinish
        (lt_of_le_of_lt (by change score + δ / 2 * s k ≤ _; linarith only [hf]) hω)
    have hpow : (1 - q) ^ Q.card ≤ Real.exp (-((Q.card : ℝ) * q)) := by
      have hbase : 1 - q ≤ Real.exp (-q) := by linarith only [Real.add_one_le_exp (-q)]
      calc
        _ ≤ (Real.exp (-q)) ^ Q.card := pow_le_pow_left₀ (sub_nonneg.mpr hq1) hbase _
        _ = _ := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
    have hprob := (measureReal_mono (μ := environmentLaw μ) hsubset)
    rw [measureReal_exists_site_above_eq] at hprob
    change 1 - (1 - q) ^ Q.card ≤ _ at hprob
    by_contra! hxk
    have hcx : c * x ≤ (Q.card : ℝ) * q := by
      calc
        _ ≤ c * (s k * ell k * q) := mul_le_mul_of_nonneg_left hxk hc.le
        _ = (c * (s k * ell k)) * q := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard hq0
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hcx)
    change (environmentLaw μ).real (endpointFastEvent g a A R (s k) (ell k) (δ / 2))
      < 1 - Real.exp (-(c * x)) at hPk
    linarith only [hprob, hpow, hexp, hPk]

end LPPDifferentiability.FinalDraft
