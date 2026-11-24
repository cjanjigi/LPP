/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.StairGeometry.Event
public import Differentiability.Probability.ClusterSizeTail
public import Differentiability.Probability.NegativeThresholdMass
public import Differentiability.Probability.ReachableSetTail
import Differentiability.FinalDraft.StairGeometry.ContourTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic

/-! # The geometry event of the very bad vertices has probability tending to one

The complement of `E_geo` is covered by one chain event (cluster-size tail) and finitely many
reachable-set events (reachable-set tail); the collars have at most `C (2 ^ k) ^ 4` vertices. -/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LPPDifferentiability

private abbrev reachS := StairGeometry.reachSet

private abbrev reachBackS := StairGeometry.reachBackSet

private def collarS (Q : Set Lattice) (c : ℕ) : Set Lattice :=
  {z | ∃ y ∈ Q, |z.1 - y.1| + |z.2 - y.2| ≤ (c : ℤ)}

private def boxS (a ℓ r : ℝ) : Set Lattice :=
  {z | |((z.1 + z.2 : ℤ) : ℝ)| ≤ ℓ ∧ |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ r}

private abbrev bigReach (m1 : ℕ) (ω : Environment) (T : ℝ) (z : Lattice) : Prop :=
  m1 ^ 2 ≤ (reachS ω T z).ncard ∧ (reachS ω T z).Finite

private abbrev bigBack (m1 : ℕ) (ω : Environment) (T : ℝ) (z : Lattice) : Prop :=
  m1 ^ 2 ≤ (reachBackS ω T z).ncard ∧ (reachBackS ω T z).Finite

private def EgeoS (K1 m1 d0 c0 : ℕ) (ω : Environment) (T : ℝ) (Q : Set Lattice) : Prop :=
  (¬ ∃ f : Fin (K1 + 1) → Lattice, Function.Injective f ∧
      (∀ i, f i ∈ collarS Q (c0 + m1 ^ 2) ∧ ω (f i) < -T) ∧
      ∀ i : Fin (K1 + 1), 0 < i.val → ∃ j : Fin (K1 + 1), j.val < i.val ∧
        |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ d0) ∧
  ∀ z ∈ collarS Q c0,
    ((reachS ω T z).Finite → (reachS ω T z).ncard < m1 ^ 2) ∧
    ((reachBackS ω T z).Finite → (reachBackS ω T z).ncard < m1 ^ 2)

private theorem boxS_finite_ncard_le (a ℓ r : ℝ) (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) :
    (boxS a ℓ r).Finite ∧ ((boxS a ℓ r).ncard : ℝ) ≤ (2 * ℓ + 3) * (2 * r + 5) := by
  have hM0 : 0 ≤ ⌈ℓ⌉ := Int.ceil_nonneg hℓ
  have hR0 : 0 ≤ ⌈r⌉ := Int.ceil_nonneg hr
  have hmaps : Set.MapsTo (fun z : Lattice => (z.1 + z.2, z.1 - ⌈a * ((z.1 + z.2 : ℤ) : ℝ)⌉))
      (boxS a ℓ r)
      ((Finset.Icc (-⌈ℓ⌉) ⌈ℓ⌉ ×ˢ Finset.Icc (-(⌈r⌉ + 1)) (⌈r⌉ + 1) : Finset (ℤ × ℤ)) :
        Set (ℤ × ℤ)) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    obtain ⟨e1, e2⟩ := abs_le.mp h1
    obtain ⟨e3, e4⟩ := abs_le.mp h2
    have c3 := Int.le_ceil ℓ
    have c4 := Int.le_ceil r
    have c1 := Int.le_ceil (a * ((z.1 + z.2 : ℤ) : ℝ))
    have c2 := Int.ceil_lt_add_one (a * ((z.1 + z.2 : ℤ) : ℝ))
    have hLe : a * ((z.1 + z.2 : ℤ) : ℝ) = a * (z.1 : ℝ) + a * (z.2 : ℝ) := by push_cast; ring
    have hL : ((z.1 + z.2 : ℤ) : ℝ) = (z.1 : ℝ) + (z.2 : ℝ) := by push_cast; ring
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
    generalize ⌈a * ((z.1 + z.2 : ℤ) : ℝ)⌉ = c at c1 c2 ⊢
    have i1 : -⌈ℓ⌉ ≤ z.1 + z.2 := by
      exact_mod_cast (show ((-⌈ℓ⌉ : ℤ) : ℝ) ≤ ((z.1 + z.2 : ℤ) : ℝ) by push_cast; linarith)
    have i2 : z.1 + z.2 ≤ ⌈ℓ⌉ := by
      exact_mod_cast (show ((z.1 + z.2 : ℤ) : ℝ) ≤ ((⌈ℓ⌉ : ℤ) : ℝ) by linarith)
    have i3 : -(⌈r⌉ + 1) ≤ z.1 - c := by
      exact_mod_cast (show ((-(⌈r⌉ + 1) : ℤ) : ℝ) ≤ ((z.1 - c : ℤ) : ℝ) by push_cast; linarith)
    have i4 : z.1 - c ≤ ⌈r⌉ + 1 := by
      exact_mod_cast (show ((z.1 - c : ℤ) : ℝ) ≤ (((⌈r⌉ + 1 : ℤ)) : ℝ) by push_cast; linarith)
    exact ⟨⟨i1, i2⟩, i3, i4⟩
  have hinj : Set.InjOn (fun z : Lattice => (z.1 + z.2, z.1 - ⌈a * ((z.1 + z.2 : ℤ) : ℝ)⌉))
      (boxS a ℓ r) := by
    intro z _ w _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1] at h2
    exact Prod.ext (by omega) (by omega)
  refine ⟨Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _), ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_product] at hle
  have hc1 : ((Finset.Icc (-⌈ℓ⌉) ⌈ℓ⌉).card : ℝ) = 2 * (⌈ℓ⌉ : ℝ) + 1 := by
    exact_mod_cast (show ((Finset.Icc (-⌈ℓ⌉) ⌈ℓ⌉).card : ℤ) = 2 * ⌈ℓ⌉ + 1 by
      rw [Int.card_Icc]; omega)
  have hc2 : ((Finset.Icc (-(⌈r⌉ + 1)) (⌈r⌉ + 1)).card : ℝ) = 2 * ((⌈r⌉ : ℝ) + 1) + 1 := by
    exact_mod_cast (show ((Finset.Icc (-(⌈r⌉ + 1)) (⌈r⌉ + 1)).card : ℤ) = 2 * (⌈r⌉ + 1) + 1 by
      rw [Int.card_Icc]; omega)
  have hR0' : (0 : ℝ) ≤ (⌈r⌉ : ℝ) := by exact_mod_cast hR0
  calc ((boxS a ℓ r).ncard : ℝ)
      ≤ ((Finset.Icc (-⌈ℓ⌉) ⌈ℓ⌉).card : ℝ) * ((Finset.Icc (-(⌈r⌉ + 1)) (⌈r⌉ + 1)).card : ℝ) := by
        exact_mod_cast hle
    _ = (2 * (⌈ℓ⌉ : ℝ) + 1) * (2 * ((⌈r⌉ : ℝ) + 1) + 1) := by rw [hc1, hc2]
    _ ≤ (2 * ℓ + 3) * (2 * r + 5) :=
        mul_le_mul (by linarith [Int.ceil_lt_add_one ℓ]) (by linarith [Int.ceil_lt_add_one r])
          (by linarith) (by linarith)

private theorem collarS_subset_boxS (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (ℓ r : ℝ) (c : ℕ) :
    collarS (boxS a ℓ r) c ⊆ boxS a (ℓ + c) (r + c) := by
  rintro z ⟨y, ⟨hy1, hy2⟩, hd⟩
  have hd' : |(z.1 : ℝ) - y.1| + |(z.2 : ℝ) - y.2| ≤ c := by
    have := (Int.cast_le (R := ℝ)).2 hd
    push_cast at this
    exact this
  obtain ⟨y1, y2⟩ := abs_le.mp hy1
  obtain ⟨y3, y4⟩ := abs_le.mp hy2
  have hyL : ((y.1 + y.2 : ℤ) : ℝ) = (y.1 : ℝ) + (y.2 : ℝ) := by push_cast; ring
  have hzL : ((z.1 + z.2 : ℤ) : ℝ) = (z.1 : ℝ) + (z.2 : ℝ) := by push_cast; ring
  have h1a : 0 ≤ 1 - a := sub_nonneg.2 ha₁.le
  have m1 := mul_le_mul_of_nonneg_left (le_abs_self ((z.1 : ℝ) - y.1)) h1a
  have m2 := mul_le_mul_of_nonneg_left (neg_abs_le ((z.1 : ℝ) - y.1)) h1a
  have m3 := mul_le_mul_of_nonneg_left (le_abs_self ((z.2 : ℝ) - y.2)) ha₀.le
  have m4 := mul_le_mul_of_nonneg_left (neg_abs_le ((z.2 : ℝ) - y.2)) ha₀.le
  have n1 := mul_nonneg ha₀.le (abs_nonneg ((z.1 : ℝ) - y.1))
  have n2 := mul_nonneg h1a (abs_nonneg ((z.2 : ℝ) - y.2))
  have q1 := le_abs_self ((z.1 : ℝ) - y.1)
  have q2 := neg_abs_le ((z.1 : ℝ) - y.1)
  have s1 := le_abs_self ((z.2 : ℝ) - y.2)
  have s2 := neg_abs_le ((z.2 : ℝ) - y.2)
  show |((z.1 + z.2 : ℤ) : ℝ)| ≤ ℓ + c ∧ |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ r + c
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

private theorem collarS_card_bound (a A B : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hA : 0 < A)
    (hB : 0 < B) (m : ℕ → ℕ) (k0 : ℕ) (hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k) (c : ℕ) :
    (∀ k : ℕ, (collarS (boxS a ((A + 5) * (2 : ℝ) ^ m k) (B * (2 : ℝ) ^ k)) c).Finite) ∧
    ∃ C : ℝ, ∀ k : ℕ, k0 ≤ k →
      ((collarS (boxS a ((A + 5) * (2 : ℝ) ^ m k) (B * (2 : ℝ) ^ k)) c).ncard : ℝ) ≤
        C * ((2 : ℝ) ^ k) ^ 4 := by
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hsub := fun k : ℕ =>
    collarS_subset_boxS a ha₀ ha₁ ((A + 5) * (2 : ℝ) ^ m k) (B * (2 : ℝ) ^ k) c
  have hbox := fun k : ℕ =>
    boxS_finite_ncard_le a ((A + 5) * (2 : ℝ) ^ m k + c) (B * (2 : ℝ) ^ k + c)
      (by positivity) (by positivity)
  refine ⟨fun k => (hbox k).1.subset (hsub k),
    (2 * (A + 5 + c) + 3) * (2 * (B + c) + 5), fun k hk => ?_⟩
  have h1 : ((collarS (boxS a ((A + 5) * (2 : ℝ) ^ m k) (B * (2 : ℝ) ^ k)) c).ncard : ℝ) ≤
      ((boxS a ((A + 5) * (2 : ℝ) ^ m k + c) (B * (2 : ℝ) ^ k + c)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard (hsub k) (hbox k).1
  have hu1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hu3 : (1 : ℝ) ≤ ((2 : ℝ) ^ k) ^ 3 := one_le_pow₀ hu1
  have hm : (2 : ℝ) ^ m k ≤ ((2 : ℝ) ^ k) ^ 3 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by have := hm3 k hk; omega)
  have e1 : 2 * ((A + 5) * (2 : ℝ) ^ m k + c) + 3 ≤ (2 * (A + 5 + c) + 3) * ((2 : ℝ) ^ k) ^ 3 := by
    linarith [mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ A + 5),
      mul_le_mul_of_nonneg_left hu3 hc]
  have e2 : 2 * (B * (2 : ℝ) ^ k + c) + 5 ≤ (2 * (B + c) + 5) * (2 : ℝ) ^ k := by
    linarith [mul_le_mul_of_nonneg_left hu1 hc]
  calc _ ≤ _ := h1
    _ ≤ (2 * ((A + 5) * (2 : ℝ) ^ m k + c) + 3) * (2 * (B * (2 : ℝ) ^ k + c) + 5) := (hbox k).2
    _ ≤ ((2 * (A + 5 + c) + 3) * ((2 : ℝ) ^ k) ^ 3) * ((2 * (B + c) + 5) * (2 : ℝ) ^ k) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = (2 * (A + 5 + c) + 3) * (2 * (B + c) + 5) * ((2 : ℝ) ^ k) ^ 4 := by ring

private theorem pT_bound (μ : Measure ℝ) [IsProbabilityMeasure μ] (p' : ℝ) (hp' : 1 < p')
    (hmom : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (K2 : ℕ) (hK2 : 1 ≤ K2) (k : ℕ) (hk : 1 ≤ k) (T : ℝ)
    (hT : T = ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ))) :
    μ.real (Iio (-T)) ≤ (∫ x, (max (-x) 0) ^ p' ∂μ) *
      ((k : ℝ) / (ε₀ / (4 * (K2 : ℝ)))) ^ p' * ((2 : ℝ) ^ k) ^ (-p') := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hK' : (0 : ℝ) < 4 * (K2 : ℝ) := mul_pos four_pos (Nat.cast_pos.mpr (by omega))
  have hu : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hε : 0 < ε₀ / (4 * (K2 : ℝ)) := div_pos hε₀ hK'
  have hkε : 0 ≤ (k : ℝ) / (ε₀ / (4 * (K2 : ℝ))) := div_nonneg hk'.le hε.le
  have hTpos : 0 < T := by rw [hT]; exact div_pos (div_pos (mul_pos hε₀ hu) hk') hK'
  have hTeq : T = (2 : ℝ) ^ k * ((k : ℝ) / (ε₀ / (4 * (K2 : ℝ))))⁻¹ := by rw [hT, inv_div]; ring
  have hTpow : T ^ (-p') = ((k : ℝ) / (ε₀ / (4 * (K2 : ℝ)))) ^ p' * ((2 : ℝ) ^ k) ^ (-p') := by
    rw [hTeq, Real.mul_rpow hu.le (inv_nonneg.mpr hkε), Real.inv_rpow hkε, Real.rpow_neg hkε,
      inv_inv]
    ring
  calc μ.real (Iio (-T)) ≤ (∫ x, (max (-x) 0) ^ p' ∂μ) * T ^ (-p') :=
        measureReal_Iio_neg_rpow_le μ T p' hTpos hp' hmom
    _ = _ := by rw [hTpow]; ring

private theorem tendsto_card_mul_rpow (C ε p' r : ℝ) (n : ℕ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hr : 0 < r) (hp : (n : ℝ) < p' * r) (Qcard : ℕ → ℕ) (pT : ℕ → ℝ)
    (hpT0 : ∀ k, 0 ≤ pT k)
    (hpT : ∀ᶠ k : ℕ in atTop, pT k ≤ C * ((k : ℝ) / ε) ^ p' * ((2 : ℝ) ^ k) ^ (-p'))
    (hQ : ∀ᶠ k : ℕ in atTop, (Qcard k : ℝ) ≤ C * ((2 : ℝ) ^ k) ^ n) :
    Tendsto (fun k : ℕ => (Qcard k : ℝ) * pT k ^ r) atTop (𝓝 0) := by
  have hb : 0 < (p' * r - n) * Real.log 2 :=
    mul_pos (by linarith) (Real.log_pos (by norm_num))
  have hlim : Tendsto (fun k : ℕ => (C * C ^ r / ε ^ (p' * r)) * ((k : ℝ) ^ (p' * r) *
      Real.exp (-((p' * r - n) * Real.log 2) * (k : ℝ)))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p' * r) _ hb).comp
      tendsto_natCast_atTop_atTop).const_mul (C * C ^ r / ε ^ (p' * r))
    rw [mul_zero] at h
    exact h
  have hrhs : ∀ k : ℕ, C * ((2 : ℝ) ^ k) ^ n *
      (C * ((k : ℝ) / ε) ^ p' * ((2 : ℝ) ^ k) ^ (-p')) ^ r =
      (C * C ^ r / ε ^ (p' * r)) * ((k : ℝ) ^ (p' * r) *
        Real.exp (-((p' * r - n) * Real.log 2) * (k : ℝ))) := by
    intro k
    have hu : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hx : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hX : 0 ≤ ((k : ℝ) / ε) ^ p' := Real.rpow_nonneg (div_nonneg hx hε.le) _
    have h2 : ((2 : ℝ) ^ k) ^ n * ((2 : ℝ) ^ k) ^ (-p' * r) =
        Real.exp (-((p' * r - n) * Real.log 2) * (k : ℝ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ k) n, ← Real.rpow_add hu, Real.rpow_def_of_pos hu,
        Real.log_pow]
      congr 1
      ring
    rw [Real.mul_rpow (mul_nonneg hC hX) (Real.rpow_nonneg hu.le _), Real.mul_rpow hC hX,
      ← Real.rpow_mul (div_nonneg hx hε.le), Real.div_rpow hx hε.le, ← Real.rpow_mul hu.le,
      ← h2]
    ring
  refine squeeze_zero' (Filter.Eventually.of_forall fun k => ?_) ?_ hlim
  · have := hpT0 k
    positivity
  · filter_upwards [hpT, hQ] with k hpk hQk
    rw [← hrhs k]
    exact mul_le_mul hQk (Real.rpow_le_rpow (hpT0 k) hpk hr.le)
      (Real.rpow_nonneg (hpT0 k) _) (by positivity)

private theorem egeo_event_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (K1 m1 d0 c0 : ℕ) (Q : Set Lattice) (F G : Finset Lattice)
    (hF : (F : Set Lattice) = collarS Q (c0 + m1 ^ 2)) (hG : (G : Set Lattice) = collarS Q c0)
    (Cr : ℝ)
    (hr : ∀ z : Lattice,
      (environmentLaw μ).real {ω | bigReach m1 ω T z} ≤ Cr * (μ.real (Iio (-T))) ^ m1 ∧
      (environmentLaw μ).real {ω | bigBack m1 ω T z} ≤ Cr * (μ.real (Iio (-T))) ^ m1) :
    (environmentLaw μ).real {ω : Environment | ¬ EgeoS K1 m1 d0 c0 ω T Q} ≤
      (F.card : ℝ) * (K1.factorial : ℝ) * (2 * (d0 : ℝ) + 1) ^ (2 * K1) *
        (μ.real (Iio (-T))) ^ (K1 + 1) +
      (G.card : ℝ) * (2 * (Cr * (μ.real (Iio (-T))) ^ m1)) := by
  have hsub : {ω : Environment | ¬ EgeoS K1 m1 d0 c0 ω T Q} ⊆
      {ω : Environment | ∃ f : Fin (K1 + 1) → Lattice, Function.Injective f ∧
        (∀ i, f i ∈ F ∧ ω (f i) < -T) ∧
        ∀ i : Fin (K1 + 1), 0 < i.val → ∃ j : Fin (K1 + 1), j.val < i.val ∧
          |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ (d0 : ℤ)} ∪
      ⋃ z ∈ G, ({ω : Environment | bigReach m1 ω T z} ∪ {ω : Environment | bigBack m1 ω T z}) := by
    intro ω (hω : ¬ EgeoS K1 m1 d0 c0 ω T Q)
    unfold EgeoS at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion]
    rcases not_and_or.mp hω with h | h
    · obtain ⟨f, hinj, hf, hch⟩ := not_not.mp h
      refine Or.inl ⟨f, hinj, fun i => ⟨?_, (hf i).2⟩, hch⟩
      have := (hf i).1
      rw [← hF] at this
      exact Finset.mem_coe.mp this
    · obtain ⟨z, h⟩ := not_forall.mp h
      obtain ⟨hz, h⟩ := not_imp.mp h
      have hzG : z ∈ G := by rw [← Finset.mem_coe, hG]; exact hz
      refine Or.inr ⟨z, hzG, ?_⟩
      rcases not_and_or.mp h with h | h
      · obtain ⟨hfin, hlt⟩ := not_imp.mp h
        exact Or.inl ⟨not_lt.mp hlt, hfin⟩
      · obtain ⟨hfin, hlt⟩ := not_imp.mp h
        exact Or.inr ⟨not_lt.mp hlt, hfin⟩
  have h1 := environmentLaw_real_close_chain_le μ T d0 K1 F
  have h2 : (environmentLaw μ).real (⋃ z ∈ G, ({ω : Environment | bigReach m1 ω T z} ∪
      {ω : Environment | bigBack m1 ω T z})) ≤
      (G.card : ℝ) * (2 * (Cr * (μ.real (Iio (-T))) ^ m1)) := by
    calc _ ≤ ∑ z ∈ G, (environmentLaw μ).real ({ω : Environment | bigReach m1 ω T z} ∪
          {ω : Environment | bigBack m1 ω T z}) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ G, 2 * (Cr * (μ.real (Iio (-T))) ^ m1) :=
          Finset.sum_le_sum fun z _ => (measureReal_union_le _ _).trans
            (by linarith [(hr z).1, (hr z).2])
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add h1 h2))

private theorem egeo_tendsto_aux (μ : Measure ℝ) [IsProbabilityMeasure μ] (p' : ℝ)
    (hp' : 1 < p') (hmom : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (A B ε₀ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε₀ : 0 < ε₀) (m1 K1 K2 : ℕ) (hm1 : 1 ≤ m1) (hK2 : 1 ≤ K2) (d0 c0 : ℕ)
    (hm1p : 4 < (m1 : ℝ) * p') (hK1p : 4 < ((K1 : ℝ) + 1) * p')
    (k0 : ℕ) (m : ℕ → ℕ) (hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k) (T : ℕ → ℝ)
    (hT : ∀ k, T k = ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ))) :
    Tendsto (fun k : ℕ => (environmentLaw μ).real {ω : Environment |
      ¬ EgeoS K1 m1 d0 c0 ω (T k) (boxS a ((A + 5) * (2 : ℝ) ^ m k) (B * (2 : ℝ) ^ k))})
      atTop (𝓝 0) := by
  have hm1pos : (0 : ℝ) < m1 := Nat.cast_pos.mpr (by omega)
  have hK2pos : (0 : ℝ) < 4 * (K2 : ℝ) := mul_pos four_pos (Nat.cast_pos.mpr (by omega))
  have hε : 0 < ε₀ / (4 * (K2 : ℝ)) := div_pos hε₀ hK2pos
  let Cr : ℝ := 2 * (6 : ℝ) ^ (4 * m1)
  let pp : ℝ := (1 / 12 : ℝ) ^ 4
  have hpp : 0 < pp := by dsimp [pp]; positivity
  obtain ⟨hfin2, C2, hC2⟩ := collarS_card_bound a A B ha₀ ha₁ hA hB m k0 hm3 (c0 + m1 ^ 2)
  obtain ⟨hfin1, C1, hC1⟩ := collarS_card_bound a A B ha₀ ha₁ hA hB m k0 hm3 c0
  choose F hF using fun k => (hfin2 k).exists_finset_coe
  choose G hG using fun k => (hfin1 k).exists_finset_coe
  obtain ⟨pT, hpTdef⟩ : ∃ pT : ℕ → ℝ, ∀ k, pT k = μ.real (Iio (-(T k))) :=
    ⟨fun k => μ.real (Iio (-(T k))), fun _ => rfl⟩
  have hpT0 : ∀ k, 0 ≤ pT k := fun k => by rw [hpTdef]; exact measureReal_nonneg
  obtain ⟨Cm, hCmdef⟩ : ∃ Cm : ℝ, Cm = ∫ x, (max (-x) 0) ^ p' ∂μ := ⟨_, rfl⟩
  obtain ⟨C, hC1', hCmC, hC1C, hC2C⟩ : ∃ C : ℝ, 1 ≤ C ∧ Cm ≤ C ∧ C1 ≤ C ∧ C2 ≤ C :=
    ⟨max (max Cm 1) (max C1 C2), le_trans (le_max_right _ _) (le_max_left _ _),
      le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hC0 : 0 ≤ C := by linarith
  have hpTev : ∀ᶠ k : ℕ in atTop,
      pT k ≤ C * ((k : ℝ) / (ε₀ / (4 * (K2 : ℝ)))) ^ p' * ((2 : ℝ) ^ k) ^ (-p') := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hb := pT_bound μ p' hp' hmom ε₀ hε₀ K2 hK2 k hk (T k) (hT k)
    rw [← hCmdef, ← hpTdef k] at hb
    have hX : 0 ≤ ((k : ℝ) / (ε₀ / (4 * (K2 : ℝ)))) ^ p' :=
      Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg k) hε.le) _
    have hY : 0 ≤ ((2 : ℝ) ^ k) ^ (-p') := Real.rpow_nonneg (by positivity) _
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCmC hX) hY)
  have hpT_tend : Tendsto pT atTop (𝓝 0) := by
    have h := tendsto_card_mul_rpow C (ε₀ / (4 * (K2 : ℝ))) p' 1 0 hC0 hε one_pos
      (by simp; linarith) (fun _ => 1) pT hpT0 hpTev
      (Filter.Eventually.of_forall fun k => by simpa using hC1')
    refine Tendsto.congr (fun k => ?_) h
    simp
  have hsmall : ∀ᶠ k : ℕ in atTop, pT k ≤ pp := hpT_tend.eventually (ge_mem_nhds hpp)
  have hQF : ∀ᶠ k : ℕ in atTop, ((F k).card : ℝ) ≤ C * ((2 : ℝ) ^ k) ^ 4 := by
    filter_upwards [eventually_ge_atTop k0] with k hk
    have h := hC2 k hk
    rw [← hF k, Set.ncard_coe_finset] at h
    exact h.trans (mul_le_mul_of_nonneg_right hC2C (by positivity))
  have hQG : ∀ᶠ k : ℕ in atTop, ((G k).card : ℝ) ≤ C * ((2 : ℝ) ^ k) ^ 4 := by
    filter_upwards [eventually_ge_atTop k0] with k hk
    have h := hC1 k hk
    rw [← hG k, Set.ncard_coe_finset] at h
    exact h.trans (mul_le_mul_of_nonneg_right hC1C (by positivity))
  have hchain := tendsto_cluster_size_tail_bound d0 K1 C (ε₀ / (4 * (K2 : ℝ))) p' hC0 hε hK1p
    (fun k => (F k).card) pT hpT0 hpTev hQF
  have hsec := tendsto_card_mul_rpow C (ε₀ / (4 * (K2 : ℝ))) p' (m1 : ℝ) 4 hC0 hε
    hm1pos (by simpa only [Nat.cast_ofNat, mul_comm] using hm1p) (fun k => (G k).card) pT hpT0 hpTev hQG
  simp only [Real.rpow_natCast] at hsec
  have hsum := hchain.add (hsec.const_mul (2 * Cr))
  rw [mul_zero, add_zero] at hsum
  refine squeeze_zero' (Filter.Eventually.of_forall fun k => measureReal_nonneg) ?_ hsum
  filter_upwards [hsmall] with k hk
  rw [hpTdef k] at hk
  have hb := egeo_event_le μ (T k) K1 m1 d0 c0
    (boxS a ((A + 5) * (2 : ℝ) ^ m k) (B * (2 : ℝ) ^ k)) (F k) (G k) (hF k) (hG k) Cr
    (fun z => StairGeometry.finite_reach_tail μ (T k) z m1 hk)
  rw [← hpTdef k] at hb
  refine hb.trans (le_of_eq ?_)
  ring

/-- Compatibility with the earlier stronger reach-tail hypothesis. -/
theorem stair_geometry_event_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ] (p' : ℝ) (hp' : 1 < p')
    (hmom : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (A B ε₀ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε₀ : 0 < ε₀) (m1 K1 K2 : ℕ) (hm1 : 1 ≤ m1) (hK1 : 1 ≤ K1) (hK2 : 1 ≤ K2)
    (hm1p : 40 < (m1 : ℝ) * p') (hK1p : 4 < ((K1 : ℝ) + 1) * p')
    (k0 : ℕ) (m : ℕ → ℕ) (hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k) :
  let θ₁ : ℝ := min a (1 - a) / 5
  let reach : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let reachBack : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let Ntr : ℕ := K1 * (2 * m1 ^ 2 + 1) ^ 2
  let W0 : ℕ := Ntr + 1
  let L : ℕ := ⌈4 * ((W0 : ℝ) + 2) / θ₁⌉₊
  let r0 : ℕ := K1 * (2 * L + 1) + Ntr
  let D1 : ℕ := ⌊2 * (W0 : ℝ) / θ₁⌋₊ + 4 * W0 + 2 * r0 + 2 * L + 8
  let d0 : ℕ := D1 + 2 * m1 ^ 2
  let c0 : ℕ := W0 + 2 * L + 1
  let collar : Set Lattice → ℕ → Set Lattice := fun Q c =>
    {z | ∃ y ∈ Q, |z.1 - y.1| + |z.2 - y.2| ≤ (c : ℤ)}
  let Egeo : Environment → ℝ → Set Lattice → Prop := fun ω T Q =>
    (¬ ∃ f : Fin (K1 + 1) → Lattice, Function.Injective f ∧
        (∀ i, f i ∈ collar Q (c0 + m1 ^ 2) ∧ ω (f i) < -T) ∧
        ∀ i : Fin (K1 + 1), 0 < i.val → ∃ j : Fin (K1 + 1), j.val < i.val ∧
          |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ d0) ∧
    ∀ z ∈ collar Q c0,
      ((reach ω T z).Finite → (reach ω T z).ncard < m1 ^ 2) ∧
      ((reachBack ω T z).Finite → (reachBack ω T z).ncard < m1 ^ 2)
  let Qk : ℕ → Set Lattice := fun k =>
    {z | |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k ∧
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ B * (2 : ℝ) ^ k}
  let Tk : ℕ → ℝ := fun k => ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ))
  Tendsto (fun k : ℕ => (environmentLaw μ).real {ω : Environment | ¬ Egeo ω (Tk k) (Qk k)})
    atTop (𝓝 0) := by
  intro _ _ _ _ _ _ _ _ d0 c0 _ _ _ _
  have _ := hK1
  exact egeo_tendsto_aux μ p' hp' hmom a ha₀ ha₁ A B ε₀ hA hB hε₀ m1 K1 K2 hm1 hK2 d0 c0
    ((by norm_num : (4 : ℝ) < 40).trans hm1p) hK1p k0 m hm3 (fun k : ℕ => ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ)))
    (fun _ => rfl)

/-- The final-draft geometry event tends to hold on the actual working region along the
record scales, for every choice of the source parameters. Final draft, Lemma `lem:stair-geometry`. -/
theorem stair_geometry_event_tendsto_final (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p' : ℝ) (hp' : 1 < p') (hmom : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (A R C₁ ε₀ ρ : ℝ)
    (hA : 0 < A) (hR : 0 < R) (hC₁ : 0 ≤ C₁) (hε₀ : 0 < ε₀) (_hρ : 1 ≤ ρ)
    (K₁ K₂ K₃ : ℕ) (_hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) (hK₃ : 1 ≤ K₃)
    (hK₃p : 4 < (K₃ : ℝ) * p') (hK₁p : 4 < ((K₁ : ℝ) + 1) * p')
    (_hK₂p : 2 * ρ + 2 < (K₂ : ℝ) * (p' - 1))
    (k0 : ℕ) (m : ℕ → ℕ) (record : Set ℕ)
    (hm3 : ∀ k, k0 ≤ k → k ∈ record → m k ≤ 3 * k) :
    Tendsto (fun k : ℕ => (environmentLaw μ).real
      (StairGeometry.goodEvent (StairGeometry.slopeCutoff a) K₁ K₃
        (StairGeometry.threshold ε₀ K₂ k) (StairGeometry.workingRegion a A R C₁ m k))ᶜ)
      (atTop ⊓ 𝓟 record) (𝓝 0) := by
  classical
  let m' (k : ℕ) := if k ∈ record then m k else 0
  have hm' (k : ℕ) (hk : k0 ≤ k) : m' k ≤ 3 * k := by
    by_cases hr : k ∈ record
    · simpa only [m', hr, ite_true] using hm3 k hk hr
    · simp [m', hr]
  have h := egeo_tendsto_aux μ p' hp' hmom a ha₀ ha₁ A (R + 2 * C₁ + 10) ε₀ hA
    (by positivity) hε₀ K₃ K₁ K₂ hK₃ hK₂
    (StairGeometry.clusterRadius (StairGeometry.slopeCutoff a) K₁ K₃)
    (StairGeometry.collarRadius (StairGeometry.slopeCutoff a) K₁ K₃)
    hK₃p hK₁p k0 m' hm' (StairGeometry.threshold ε₀ K₂) (fun _ => rfl)
  refine (h.mono_left inf_le_left).congr' ?_
  filter_upwards [(eventually_mem_principal record).filter_mono inf_le_right] with k hk
  have hmk : m' k = m k := ite_eq_left hk
  simp only [hmk, EgeoS, StairGeometry.goodEvent, StairGeometry.noLongChain,
    StairGeometry.collar, collarS, boxS, StairGeometry.workingRegion,
    StairGeometry.latticeDistance, Set.compl_ofPred, Set.mem_ofPred_eq]

/-- Both source collars have finitely many sites at every scale. -/
theorem stair_working_collars_finite (a A R C₁ : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hA : 0 < A) (hR : 0 < R) (hC₁ : 0 ≤ C₁) (m : ℕ → ℕ) (c k : ℕ) :
    (StairGeometry.collar (StairGeometry.workingRegion a A R C₁ m k) c).Finite := by
  apply Set.Finite.subset (boxS_finite_ncard_le a _ _
    (show 0 ≤ (A + 5) * (2 : ℝ) ^ m k + c by positivity)
    (show 0 ≤ (R + 2 * C₁ + 10) * (2 : ℝ) ^ k + c by positivity)).1
  exact collarS_subset_boxS a ha₀ ha₁ _ _ c

end LPPDifferentiability
