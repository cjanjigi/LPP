/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.GlobalMaskFamilyWeights
public import Differentiability.Probability.NegativeThresholdMass
public import Differentiability.Analysis.StaircaseWeightDecay
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Staircases with a heavy lower tail

This file formalizes the heavy-lower-tail staircase bound in Lemma B.6 of the differentiability
preprint, under its parameter condition (B.7).

For every scale `k` let a finite family of at most `(2^k)^q` members be given in the shape of the
global-mask weight theorems: each active member collects at most `8 c* k^2 2^k` sites, all in a
finite region, none of them very bad at the level `T_k = ε₀ 2^k / k / (4 K₂)`, and the family is a
function of the Boolean very-bad mask with the measurability hypothesis of those theorems. If
`K₂ (p' - 1) > 2 q + 2` (the third condition in (B.7)), the probability
that some member has weight below `-2 Cm |α| - t_k / 2`, with `t_k = ε₀ 2^k / k`, tends to `0`.

The proof applies `global_mask_family_weight_failure_le` (resp. the path version) with
`b = (2^k)^(1 - ε')`, `ε' = (p' - 1) / (2 p')`, `t = t_k / 4` and `K = K₂`, and then the two scalar
limits `staircase_weight_polynomial_decay` and `staircase_weight_stretched_exponential_decay` with
constant `32`.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace LPPDifferentiability

private theorem stair_K2_one_le (p' q : ℝ) (hq : 1 ≤ q) (K2 : ℕ)
    (hK2 : 2 * q + 2 < (K2 : ℝ) * (p' - 1)) : 1 ≤ K2 := by
  by_contra h
  have hK0 : K2 = 0 := by omega
  subst hK0
  simp at hK2
  linarith

/-- `(K₂ - 1) T_k + t_k / 4 ≤ t_k / 2` for `T_k = t_k / (4 K₂)`. -/
private theorem stair_threshold_le (ε₀ : ℝ) (hε₀ : 0 < ε₀) (K2 : ℕ) (hK : 1 ≤ K2) (k : ℕ)
    (hk : 1 ≤ k) :
    ((K2 - 1 : ℕ) : ℝ) * (ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ))) +
      ε₀ * (2 : ℝ) ^ k / (k : ℝ) / 4 ≤ ε₀ * (2 : ℝ) ^ k / (k : ℝ) / 2 := by
  have hK0 : (0 : ℝ) < K2 := by exact_mod_cast hK
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set u : ℝ := ε₀ * (2 : ℝ) ^ k / (k : ℝ) with hu
  have hu0 : 0 < u := by positivity
  have h1 : ((K2 - 1 : ℕ) : ℝ) * (u / (4 * (K2 : ℝ))) = u / 4 - u / (4 * (K2 : ℝ)) := by
    rw [Nat.cast_sub hK, Nat.cast_one]
    field_simp
  have h2 : 0 ≤ u / (4 * (K2 : ℝ)) := by positivity
  rw [h1]
  linarith

private theorem two_pow_div_atTop :
    Tendsto (fun k : ℕ => (2 : ℝ) ^ k / (k : ℝ)) atTop atTop := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < (k : ℝ) ^ 1 / (2 : ℝ) ^ k := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have h' : Tendsto (fun k : ℕ => (k : ℝ) ^ 1 / (2 : ℝ) ^ k) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨h, hpos⟩
  refine (tendsto_inv_nhdsGT_zero.comp h').congr fun k => ?_
  simp [inv_div]

private theorem stair_limit
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p' : ℝ) (hp' : 1 < p')
    (ε₀ cstar q : ℝ) (hε₀ : 0 < ε₀) (hcstar : 0 < cstar) (hq : 1 ≤ q)
    (K2 : ℕ) (hK2 : 2 * q + 2 < (K2 : ℝ) * (p' - 1))
    (k0 : ℕ) (N : ℕ → ℕ) (hN : ∀ k, k0 ≤ k → (N k : ℝ) ≤ ((2 : ℝ) ^ k) ^ q)
    (X : ℕ → ℝ) (hX0 : ∀ k, 0 ≤ X k)
    (hX : ∀ k, k0 ≤ k → 1 ≤ k →
      2⁻¹ ≤ μ (Set.Ici (-(ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ))))) →
      X k ≤ (N k : ℝ) *
        ((2 * ((⌊8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k⌋₊ : ℕ) : ℝ) *
            (∫ y, (max (-y) 0) ^ p' ∂μ) *
            (((2 : ℝ) ^ k) ^ (1 - (p' - 1) / (2 * p'))) ^ (-p')) ^ K2 +
          Real.exp (-(ε₀ * (2 : ℝ) ^ k / (k : ℝ) / 4) ^ 2 /
            (2 * ((2 : ℝ) ^ k) ^ (1 - (p' - 1) / (2 * p')) *
              (2 * (∫ y, max (-y) 0 ∂μ) *
                ((⌊8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k⌋₊ : ℕ) : ℝ) +
                (ε₀ * (2 : ℝ) ^ k / (k : ℝ) / 4) / 3))))) :
    Tendsto X atTop (𝓝 0) := by
  have hK2one : (1 : ℝ) ≤ K2 := by exact_mod_cast stair_K2_one_le p' q hq K2 hK2
  have hK2pos : (0 : ℝ) < K2 := by linarith
  set Cp : ℝ := ∫ y, (max (-y) 0) ^ p' ∂μ with hCpdef
  set Cm : ℝ := ∫ y, max (-y) 0 ∂μ with hCmdef
  have hCp : 0 ≤ Cp := integral_nonneg fun y => Real.rpow_nonneg (le_max_right _ _) _
  have hCm : 0 ≤ Cm := integral_nonneg fun y => le_max_right _ _
  set e : ℝ := (p' - 1) / (2 * p') with hedef
  have hp0 : 0 < p' := by linarith
  have he : 0 < e := div_pos (by linarith) (by linarith)
  set M : ℝ := 16 * cstar * Cm + ε₀ / 12 with hMdef
  have hM : 0 < M := by positivity
  set c : ℝ := ε₀ ^ 2 / (32 * M) with hcdef
  have hc : 0 < c := by positivity
  have hf1 := staircase_weight_polynomial_decay (p := p') (q := q) (cstar := cstar) (Cp := Cp)
    (K := K2) hp' hq hcstar hCp hK2
  have hf2 := staircase_weight_stretched_exponential_decay (q := q) (c := c) (epsilon := e)
    hq hc he
  have hthr : ∀ᶠ k : ℕ in atTop,
      2⁻¹ ≤ μ (Set.Ici (-(ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ))))) := by
    have h := (eventually_measure_Ici_sourceScale_ge_half μ (16 * ε₀) (K2 : ℝ)
      (by positivity) hK2one)
    filter_upwards [two_pow_div_atTop.eventually h, eventually_gt_atTop (0 : ℕ)] with k hk hkpos
    have hk' : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hK' : (0 : ℝ) < K2 := hK2pos
    have heq : 16 * ε₀ * ((2 : ℝ) ^ k / (k : ℝ)) / (64 * (K2 : ℝ)) =
        ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ)) := by
      field_simp
      ring
    rwa [heq] at hk
  refine squeeze_zero' (Eventually.of_forall hX0) ?_ (by simpa using hf1.add hf2)
  filter_upwards [hthr, eventually_ge_atTop (max k0 1)] with k hk hkk
  have hk0 : k0 ≤ k := le_trans (le_max_left _ _) hkk
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hkk
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkpos : (0 : ℝ) < k := by linarith
  set s : ℝ := (2 : ℝ) ^ k with hsdef
  have hs : 0 < s := by positivity
  set n : ℕ := ⌊8 * cstar * (k : ℝ) ^ 2 * s⌋₊ with hndef
  have hnle : (n : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * s := Nat.floor_le (by positivity)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set b : ℝ := s ^ (1 - e) with hbdef
  have hb : 0 < b := Real.rpow_pos_of_pos hs _
  have hbp : b ^ (-p') = s ^ (-(p' + 1) / 2) := by
    rw [hbdef, ← Real.rpow_mul hs.le]
    congr 1
    rw [hedef]
    field_simp
    ring
  have hsbp : s * b ^ (-p') = s ^ ((1 - p') / 2) := by
    rw [hbp, show s * s ^ (-(p' + 1) / 2) = s ^ (1 : ℝ) * s ^ (-(p' + 1) / 2) by
      rw [Real.rpow_one], ← Real.rpow_add hs]
    congr 1
    ring
  have hbs : b * s ^ e = s := by
    rw [hbdef, ← Real.rpow_add hs]
    simp
  have hmain := hX k hk0 hk1 hk
  refine hmain.trans ?_
  have hA : 2 * (n : ℝ) * Cp * b ^ (-p') ≤
      16 * cstar * Cp * (k : ℝ) ^ 2 * s ^ ((1 - p') / 2) := by
    have hbpos : 0 ≤ b ^ (-p') := Real.rpow_nonneg hb.le _
    calc 2 * (n : ℝ) * Cp * b ^ (-p') ≤ 2 * (8 * cstar * (k : ℝ) ^ 2 * s) * Cp * b ^ (-p') := by
          gcongr
      _ = 16 * cstar * Cp * (k : ℝ) ^ 2 * (s * b ^ (-p')) := by ring
      _ = _ := by rw [hsbp]
  have hA0 : 0 ≤ 2 * (n : ℝ) * Cp * b ^ (-p') := by
    have := Real.rpow_nonneg hb.le (-p')
    positivity
  have ht : 0 < ε₀ * s / (k : ℝ) / 4 := by positivity
  have hd : 0 < 2 * b * (2 * Cm * (n : ℝ) + (ε₀ * s / (k : ℝ) / 4) / 3) := by positivity
  have hdle : 2 * b * (2 * Cm * (n : ℝ) + (ε₀ * s / (k : ℝ) / 4) / 3) ≤
      2 * b * (s * (k : ℝ) ^ 2 * M) := by
    have h1 : 2 * Cm * (n : ℝ) ≤ 2 * Cm * (8 * cstar * (k : ℝ) ^ 2 * s) := by gcongr
    have h2 : (ε₀ * s / (k : ℝ) / 4) / 3 ≤ ε₀ * s * (k : ℝ) ^ 2 / 12 := by
      have hk2 : (1 : ℝ) / k ≤ (k : ℝ) ^ 2 := by
        rw [div_le_iff₀ hkpos]; nlinarith
      calc (ε₀ * s / (k : ℝ) / 4) / 3 = ε₀ * s * (1 / (k : ℝ)) / 12 := by ring
        _ ≤ ε₀ * s * (k : ℝ) ^ 2 / 12 := by gcongr
    have h3 : 2 * Cm * (8 * cstar * (k : ℝ) ^ 2 * s) + ε₀ * s * (k : ℝ) ^ 2 / 12 =
        s * (k : ℝ) ^ 2 * M := by rw [hMdef]; ring
    gcongr
    linarith
  have hexp : c * s ^ e / (k : ℝ) ^ 4 ≤
      (ε₀ * s / (k : ℝ) / 4) ^ 2 /
        (2 * b * (2 * Cm * (n : ℝ) + (ε₀ * s / (k : ℝ) / 4) / 3)) := by
    rw [le_div_iff₀ hd]
    have hk4 : 0 < (k : ℝ) ^ 4 := by positivity
    calc c * s ^ e / (k : ℝ) ^ 4 * (2 * b * (2 * Cm * (n : ℝ) + (ε₀ * s / (k : ℝ) / 4) / 3))
        ≤ c * s ^ e / (k : ℝ) ^ 4 * (2 * b * (s * (k : ℝ) ^ 2 * M)) := by
          gcongr
      _ = (ε₀ * s / (k : ℝ) / 4) ^ 2 := by
          have : c * s ^ e / (k : ℝ) ^ 4 * (2 * b * (s * (k : ℝ) ^ 2 * M)) =
              c * (2 * M) * (b * s ^ e) * s / (k : ℝ) ^ 2 := by
            field_simp
          rw [this, hbs, hcdef]
          field_simp
          ring
  have hE : Real.exp (-(ε₀ * s / (k : ℝ) / 4) ^ 2 /
        (2 * b * (2 * Cm * (n : ℝ) + (ε₀ * s / (k : ℝ) / 4) / 3))) ≤
      Real.exp (-c * s ^ e / (k : ℝ) ^ 4) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_mul, neg_div]
    exact neg_le_neg hexp
  have hNs := hN k hk0
  have hNn : (0 : ℝ) ≤ N k := Nat.cast_nonneg _
  have hsq : 0 ≤ s ^ q := Real.rpow_nonneg hs.le q
  calc (N k : ℝ) * ((2 * (n : ℝ) * Cp * b ^ (-p')) ^ K2 + Real.exp (-(ε₀ * s / (k : ℝ) / 4) ^ 2 /
        (2 * b * (2 * Cm * (n : ℝ) + (ε₀ * s / (k : ℝ) / 4) / 3))))
      ≤ s ^ q * ((16 * cstar * Cp * (k : ℝ) ^ 2 * s ^ ((1 - p') / 2)) ^ K2 +
        Real.exp (-c * s ^ e / (k : ℝ) ^ 4)) := by
        refine mul_le_mul hNs (add_le_add ?_ hE) (by positivity) hsq
        exact pow_le_pow_left₀ hA0 hA K2
    _ = _ := by rw [mul_add, neg_mul]

/-- Staircases with a heavy lower tail, as in Lemma B.6 of the differentiability preprint, under
its parameter condition (B.7). -/
theorem staircase_general_family_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p' : ℝ) (hp' : 1 < p')
    (hmom : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (ε₀ cstar q : ℝ) (hε₀ : 0 < ε₀) (hcstar : 0 < cstar) (hq : 1 ≤ q)
    (K2 : ℕ) (hK2 : 2 * q + 2 < (K2 : ℝ) * (p' - 1))
    (k0 : ℕ) (Q : ℕ → Set Lattice) (hQ : ∀ k, (Q k).Finite)
    (J : ℕ → Type*) [∀ k, Fintype (J k)]
    (hcard : ∀ k, k0 ≤ k → (Fintype.card (J k) : ℝ) ≤ ((2 : ℝ) ^ k) ^ q)
    (active : ∀ k, (Lattice → Bool) → J k → Bool)
    (sites : ∀ k, (Lattice → Bool) → J k → Finset Lattice)
    (hlen : ∀ k a j, active k a j = true →
      ((sites k a j).card : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k)
    (hmem : ∀ k a j, active k a j = true → ∀ z ∈ sites k a j, z ∈ Q k)
    (hgood : ∀ k a j, active k a j = true → ∀ z ∈ sites k a j, a z = false)
    (hmeas : ∀ k (j : J k) (s : Finset Lattice),
      MeasurableSet {a : Lattice → Bool | active k a j = true ∧ sites k a j = s}) :
    let Cm : ℝ := ∫ y, max (-y) 0 ∂μ
    let Tk : ℕ → ℝ := fun k => ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ))
    let tk : ℕ → ℝ := fun k => ε₀ * (2 : ℝ) ^ k / (k : ℝ)
    let mask : ℕ → Environment → Lattice → Bool :=
      fun k ω z => if ω z < -Tk k then true else false
    Tendsto (fun k : ℕ => (environmentLaw μ).real {ω : Environment |
      ∃ j : J k, active k (mask k ω) j = true ∧
        ∑ z ∈ sites k (mask k ω) j, ω z <
          -2 * Cm * ((sites k (mask k ω) j).card : ℝ) - tk k / 2})
      atTop (𝓝 0) := by
  classical
  intro Cm Tk tk mask
  have hK1 : 1 ≤ K2 := stair_K2_one_le p' q hq K2 hK2
  refine stair_limit μ p' hp' ε₀ cstar q hε₀ hcstar hq K2 hK2 k0
    (fun k => Fintype.card (J k)) hcard _ (fun k => measureReal_nonneg) ?_
  intro k hk0 hk1 hthr
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hK0 : (0 : ℝ) < K2 := by exact_mod_cast hK1
  have hT : 0 < Tk k := by positivity
  have hb : 0 < ((2 : ℝ) ^ k) ^ (1 - (p' - 1) / (2 * p')) :=
    Real.rpow_pos_of_pos (by positivity) _
  have ht : 0 < ε₀ * (2 : ℝ) ^ k / (k : ℝ) / 4 := by positivity
  have h := global_mask_family_weight_failure_le μ (Tk k) p'
    (((2 : ℝ) ^ k) ^ (1 - (p' - 1) / (2 * p'))) (ε₀ * (2 : ℝ) ^ k / (k : ℝ) / 4)
    hp' hT hthr hb ht hmom (hQ k).toFinset ⌊8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k⌋₊
    (Fintype.card (J k)) K2 hK1 le_rfl (active k) (sites k)
    (fun a j hj => Nat.le_floor (hlen k a j hj))
    (fun a j hj z hz => (Set.Finite.mem_toFinset _).2 (hmem k a j hj z hz))
    (hgood k) (hmeas k)
  refine le_trans (measureReal_mono ?_) h.2
  rintro ω ⟨j, hact, hlt⟩
  refine ⟨j, hact, lt_of_lt_of_le hlt ?_⟩
  have := stair_threshold_le ε₀ hε₀ K2 hK1 k hk1
  show -2 * Cm * ((sites k (mask k ω) j).card : ℝ) - tk k / 2 ≤
    -2 * Cm * ((sites k (mask k ω) j).card : ℝ) - ((K2 - 1 : ℕ) : ℝ) * Tk k -
      ε₀ * (2 : ℝ) ^ k / (k : ℝ) / 4
  linarith

/-- The same statement for actual paths, in the shape of
`global_mask_path_weight_failure_le`. The family of paths may depend on the whole mask; the
collected vertices of an active member are the vertices `i.castSucc` of its path. -/
theorem staircase_general_path_family_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p' : ℝ) (hp' : 1 < p')
    (hmom : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (ε₀ cstar q : ℝ) (hε₀ : 0 < ε₀) (hcstar : 0 < cstar) (hq : 1 ≤ q)
    (K2 : ℕ) (hK2 : 2 * q + 2 < (K2 : ℝ) * (p' - 1))
    (k0 : ℕ) (Q : ℕ → Set Lattice) (hQ : ∀ k, (Q k).Finite)
    (J : ℕ → Type*) [∀ k, Fintype (J k)]
    (hcard : ∀ k, k0 ≤ k → (Fintype.card (J k) : ℝ) ≤ ((2 : ℝ) ^ k) ^ q)
    (active : ∀ k, (Lattice → Bool) → J k → Bool)
    (starts : ∀ k, (Lattice → Bool) → J k → Lattice)
    (disps : ∀ k, (Lattice → Bool) → J k → ℕ × ℕ)
    (pa : ∀ k (a : Lattice → Bool) (j : J k), Path (starts k a j) (disps k a j))
    (hlen : ∀ k a j, active k a j = true →
      (((disps k a j).1 + (disps k a j).2 : ℕ) : ℝ) ≤
        8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k)
    (hmem : ∀ k a j, active k a j = true → ∀ i : Fin ((disps k a j).1 + (disps k a j).2),
      (pa k a j).vertex i.castSucc ∈ Q k)
    (hgood : ∀ k a j, active k a j = true → ∀ i : Fin ((disps k a j).1 + (disps k a j).2),
      a ((pa k a j).vertex i.castSucc) = false)
    (hmeas : ∀ k (j : J k) (s : Finset Lattice), MeasurableSet {a : Lattice → Bool |
      active k a j = true ∧ Finset.univ.image
        (fun i : Fin ((disps k a j).1 + (disps k a j).2) =>
          (pa k a j).vertex i.castSucc) = s}) :
    let Cm : ℝ := ∫ y, max (-y) 0 ∂μ
    let Tk : ℕ → ℝ := fun k => ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ))
    let tk : ℕ → ℝ := fun k => ε₀ * (2 : ℝ) ^ k / (k : ℝ)
    let mask : ℕ → Environment → Lattice → Bool :=
      fun k ω z => if ω z < -Tk k then true else false
    Tendsto (fun k : ℕ => (environmentLaw μ).real {ω : Environment |
      ∃ j : J k, active k (mask k ω) j = true ∧
        pathWeight ω (pa k (mask k ω) j) <
          -2 * Cm * ((disps k (mask k ω) j).1 + (disps k (mask k ω) j).2) - tk k / 2})
      atTop (𝓝 0) := by
  classical
  intro Cm Tk tk mask
  have hK1 : 1 ≤ K2 := stair_K2_one_le p' q hq K2 hK2
  refine stair_limit μ p' hp' ε₀ cstar q hε₀ hcstar hq K2 hK2 k0
    (fun k => Fintype.card (J k)) hcard _ (fun k => measureReal_nonneg) ?_
  intro k hk0 hk1 hthr
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hK0 : (0 : ℝ) < K2 := by exact_mod_cast hK1
  have hT : 0 < Tk k := by positivity
  have hb : 0 < ((2 : ℝ) ^ k) ^ (1 - (p' - 1) / (2 * p')) :=
    Real.rpow_pos_of_pos (by positivity) _
  have ht : 0 < ε₀ * (2 : ℝ) ^ k / (k : ℝ) / 4 := by positivity
  have h := global_mask_path_weight_failure_le μ (Tk k) p'
    (((2 : ℝ) ^ k) ^ (1 - (p' - 1) / (2 * p'))) (ε₀ * (2 : ℝ) ^ k / (k : ℝ) / 4)
    hp' hT hthr hb ht hmom (hQ k).toFinset ⌊8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k⌋₊
    (Fintype.card (J k)) K2 hK1 le_rfl (active k) (starts k) (disps k) (pa k)
    (fun a j hj => Nat.le_floor (hlen k a j hj))
    (fun a j hj i => (Set.Finite.mem_toFinset _).2 (hmem k a j hj i))
    (hgood k) (hmeas k)
  refine le_trans (measureReal_mono ?_) h.2
  rintro ω ⟨j, hact, hlt⟩
  refine ⟨j, hact, lt_of_lt_of_le hlt ?_⟩
  have := stair_threshold_le ε₀ hε₀ K2 hK1 k hk1
  show -2 * Cm * (((disps k (mask k ω) j).1 : ℝ) + ((disps k (mask k ω) j).2 : ℝ)) - tk k / 2 ≤
    -2 * Cm * (((disps k (mask k ω) j).1 : ℝ) + ((disps k (mask k ω) j).2 : ℝ)) -
      ((K2 - 1 : ℕ) : ℝ) * Tk k - ε₀ * (2 : ℝ) ^ k / (k : ℝ) / 4
  linarith

end LPPDifferentiability
