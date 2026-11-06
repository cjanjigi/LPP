/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.FiniteContourBadLabels
import Mathlib.Tactic

/-!
# Peierls bound for coarse paths

A finite-range Peierls bound for oriented coarse paths with few good sites.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- An oriented path with `m` steps from the origin, as a list of its `m + 1` sites. -/
private abbrev IsOrientedPath (m : ℕ) (q : Fin (m + 1) → ℕ × ℕ) : Prop :=
  q 0 = (0, 0) ∧ ∀ i : Fin m, q i.succ = q i.castSucc + (1, 0) ∨
    q i.succ = q i.castSucc + (0, 1)

/-- Site number `j` of an oriented path has coordinate sum `j`. -/
private theorem oriented_path_sum {m : ℕ} {q : Fin (m + 1) → ℕ × ℕ}
    (hq : IsOrientedPath m q) :
    ∀ (j : ℕ) (hj : j < m + 1), (q ⟨j, hj⟩).1 + (q ⟨j, hj⟩).2 = j := by
  intro j
  induction j with
  | zero =>
    intro hj
    have e : (⟨0, hj⟩ : Fin (m + 1)) = 0 := Fin.ext (by simp)
    rw [e, hq.1]
    simp
  | succ j ih =>
    intro hj
    have hs : q ⟨j + 1, hj⟩ = q ⟨j, by omega⟩ + (1, 0) ∨
        q ⟨j + 1, hj⟩ = q ⟨j, by omega⟩ + (0, 1) := hq.2 ⟨j, by omega⟩
    have ihj := ih (by omega)
    rcases hs with hs | hs <;> rw [hs] <;> simp <;> omega

/-- The sites of an oriented path are distinct. -/
private theorem oriented_path_injective {m : ℕ} {q : Fin (m + 1) → ℕ × ℕ}
    (hq : IsOrientedPath m q) : Function.Injective q := by
  intro a b hab
  have ha : (q a).1 + (q a).2 = a.1 := oriented_path_sum hq a.1 a.2
  have hb : (q b).1 + (q b).2 = b.1 := oriented_path_sum hq b.1 b.2
  have hab' : (q a).1 + (q a).2 = (q b).1 + (q b).2 := by rw [hab]
  exact Fin.ext (by omega)

/-- There are at most `2 ^ m` oriented paths with `m` steps. -/
private theorem oriented_path_finset (m : ℕ) :
    ∃ Qf : Finset (Fin (m + 1) → ℕ × ℕ),
      (∀ q, IsOrientedPath m q ↔ q ∈ Qf) ∧ Qf.card ≤ 2 ^ m := by
  let φ : (Fin (m + 1) → ℕ × ℕ) → (Fin m → Bool) :=
    fun q i => decide (q i.succ = q i.castSucc + (1, 0))
  have hinj : Set.InjOn φ {q | IsOrientedPath m q} := by
    intro q hq q' hq' h
    have hext : ∀ (j : ℕ) (hj : j < m + 1), q ⟨j, hj⟩ = q' ⟨j, hj⟩ := by
      intro j
      induction j with
      | zero =>
        intro hj
        have e : (⟨0, hj⟩ : Fin (m + 1)) = 0 := Fin.ext (by simp)
        rw [e, hq.1, hq'.1]
      | succ j ih =>
        intro hj
        have ihj := ih (by omega)
        have hs : q ⟨j + 1, hj⟩ = q ⟨j, by omega⟩ + (1, 0) ∨
            q ⟨j + 1, hj⟩ = q ⟨j, by omega⟩ + (0, 1) := hq.2 ⟨j, by omega⟩
        have hs' : q' ⟨j + 1, hj⟩ = q' ⟨j, by omega⟩ + (1, 0) ∨
            q' ⟨j + 1, hj⟩ = q' ⟨j, by omega⟩ + (0, 1) := hq'.2 ⟨j, by omega⟩
        have hd : decide (q ⟨j + 1, hj⟩ = q ⟨j, by omega⟩ + (1, 0)) =
            decide (q' ⟨j + 1, hj⟩ = q' ⟨j, by omega⟩ + (1, 0)) :=
          congrFun h ⟨j, by omega⟩
        have hh := decide_eq_decide.mp hd
        rcases hs with hs | hs
        · rw [hs, hh.mp hs, ihj]
        · rcases hs' with hs' | hs'
          · have h10 := hh.mpr hs'
            have : ((0, 1) : ℕ × ℕ) = (1, 0) := add_left_cancel (hs.symm.trans h10)
            simp at this
          · rw [hs, hs', ihj]
    funext i
    exact hext i.1 i.2
  have hfin : Set.Finite {q | IsOrientedPath m q} :=
    Set.Finite.of_finite_image (Set.toFinite _) hinj
  refine ⟨hfin.toFinset, fun q => by simp, ?_⟩
  calc hfin.toFinset.card = (hfin.toFinset.image φ).card :=
        (Finset.card_image_of_injOn (by simpa using hinj)).symm
    _ ≤ Fintype.card (Fin m → Bool) := Finset.card_le_univ _
    _ = 2 ^ m := by simp

private theorem two_pow_mul_eighth_pow (m : ℕ) :
    (2 : ℝ) ^ m * (2 ^ (m + 1) * (1 / 8) ^ m) = 2 * (2⁻¹ : ℝ) ^ m := by
  have h8 : (1 / 8 : ℝ) ^ m = (2⁻¹ : ℝ) ^ m * (2⁻¹ : ℝ) ^ m * (2⁻¹ : ℝ) ^ m := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have hxy : (2 : ℝ) ^ m * (2⁻¹ : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  rw [h8, pow_succ]
  calc (2 : ℝ) ^ m * (2 ^ m * 2 * ((2⁻¹ : ℝ) ^ m * (2⁻¹ : ℝ) ^ m * (2⁻¹ : ℝ) ^ m))
      = 2 * ((2 : ℝ) ^ m * (2⁻¹ : ℝ) ^ m) * ((2 : ℝ) ^ m * (2⁻¹ : ℝ) ^ m) *
          (2⁻¹ : ℝ) ^ m := by ring
    _ = 2 * (2⁻¹ : ℝ) ^ m := by rw [hxy]; ring

open Classical in
/-- For each dependence range and density below one there is a cutoff on the failure
probability of the site events. Below it, oriented paths from the origin with at most
that density of good sites have exponentially small probability. -/
theorem exists_sparse_good_coarse_path_cutoff (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (k : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (G : ℕ × ℕ → Set Ω),
        (∀ v, MeasurableSet (G v)) →
        (∀ v, P.real ((G v)ᶜ) ≤ ζ) →
        (∀ T : Finset (ℕ × ℕ),
          (∀ u ∈ T, ∀ v ∈ T, u ≠ v →
            k < Nat.dist u.1 v.1 ∨ k < Nat.dist u.2 v.2) →
          iIndepSet (fun v : {u : ℕ × ℕ // u ∈ T} => G v.1) P) →
        ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ m : ℕ, 1 ≤ m →
          P.real {ω : Ω | ∃ q : Fin (m + 1) → ℕ × ℕ, q 0 = (0, 0) ∧
            (∀ i : Fin m, q i.succ = q i.castSucc + (1, 0) ∨
              q i.succ = q i.castSucc + (0, 1)) ∧
            ((Finset.univ.filter fun j => ω ∈ G (q j)).card : ℝ) ≤ ρ * (m + 1)} ≤
            a * Real.exp (-(b * m)) := by
  -- the density is positive in the statement; the bound itself does not need it
  have _hρ₀ := hρ₀
  have hD : (0 : ℝ) < (((2 * k + 1) ^ 2 : ℕ) : ℝ) := by positivity
  have hρ' : 0 < 1 - ρ := sub_pos.mpr hρ₁
  set κ : ℝ := (1 - ρ) / (((2 * k + 1) ^ 2 : ℕ) : ℝ) with hκ
  have hκpos : 0 < κ := div_pos hρ' hD
  refine ⟨(1 / 8 : ℝ) ^ (1 / κ), by positivity,
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity), ?_⟩
  intro Ω _ P _ G hG hMarg hIndep
  set ζ : ℝ := (1 / 8 : ℝ) ^ (1 / κ) with hζdef
  have hζpos : 0 < ζ := by positivity
  have hζlt : ζ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  have hζκ : ζ ^ κ = 1 / 8 := by
    rw [hζdef, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hκpos.ne', Real.rpow_one]
  refine ⟨2, Real.log 2, by norm_num, Real.log_pos (by norm_num), ?_⟩
  intro m _
  have hexp : Real.exp (-(Real.log 2 * m)) = (2⁻¹ : ℝ) ^ m := by
    rw [show -(Real.log 2 * (m : ℝ)) = (m : ℝ) * (-Real.log 2) by ring, Real.exp_nat_mul,
      Real.exp_neg, Real.exp_log (by norm_num)]
  rw [hexp]
  -- the number of sites that must fail
  set b : ℕ := ⌈(1 - ρ) * ((m : ℝ) + 1)⌉₊ with hb
  have hbge : (1 - ρ) * ((m : ℝ) + 1) ≤ b := Nat.le_ceil _
  -- each fixed set of `b` sites all fail with probability at most `8⁻ᵐ`
  have hset : ∀ S : Finset (ℕ × ℕ), S.card = b →
      P.real {ω : Ω | ∀ v ∈ S, ω ∉ G v} ≤ (1 / 8 : ℝ) ^ m := by
    intro S hS
    have h1 := measure_all_bad_natural_sites_le_real_power P G hG k (8 * b) ζ hζpos hζlt
      (fun v _ => hMarg v) hIndep S (by omega)
    refine h1.trans ?_
    have hexpo : κ * (m : ℝ) ≤ ((8 * b : ℕ) : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)) := by
      rw [hκ, div_mul_eq_mul_div, div_le_div_iff₀ hD (by positivity)]
      have h2 : (1 - ρ) * (m : ℝ) ≤ b := by nlinarith
      have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))
      push_cast at h3 ⊢
      linarith
    calc Real.rpow ζ (((8 * b : ℕ) : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))
        ≤ Real.rpow ζ (κ * (m : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hζpos hζlt.le hexpo
      _ = (1 / 8 : ℝ) ^ m := by
          change ζ ^ (κ * (m : ℝ)) = _
          rw [Real.rpow_mul_natCast hζpos.le, hζκ]
  obtain ⟨Qf, hQf, hQcard⟩ := oriented_path_finset m
  -- the covering by fixed all-failing site sets
  let Fq : (Fin (m + 1) → ℕ × ℕ) → Set Ω := fun q =>
    ⋃ S ∈ (Finset.univ.image q).powersetCard b, {ω : Ω | ∀ v ∈ S, ω ∉ G v}
  have hcover : {ω : Ω | ∃ q : Fin (m + 1) → ℕ × ℕ, q 0 = (0, 0) ∧
            (∀ i : Fin m, q i.succ = q i.castSucc + (1, 0) ∨
              q i.succ = q i.castSucc + (0, 1)) ∧
            ((Finset.univ.filter fun j => ω ∈ G (q j)).card : ℝ) ≤ ρ * (m + 1)} ⊆
      ⋃ q ∈ Qf, Fq q := by
    intro ω ⟨q, h0, hstep, hcount⟩
    have hqp : IsOrientedPath m q := ⟨h0, hstep⟩
    simp only [Set.mem_iUnion]
    refine ⟨q, (hQf q).mp hqp, ?_⟩
    simp only [Fq, Set.mem_iUnion]
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (m + 1))))
      (fun j => ω ∈ G (q j))
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    have hsumR : ((Finset.univ.filter fun j => ω ∈ G (q j)).card : ℝ) +
        ((Finset.univ.filter fun j => ¬ ω ∈ G (q j)).card : ℝ) = (m : ℝ) + 1 := by
      exact_mod_cast hsum
    have hJ : b ≤ (Finset.univ.filter fun j => ¬ ω ∈ G (q j)).card := by
      rw [hb]
      apply Nat.ceil_le.mpr
      nlinarith
    obtain ⟨J', hJ'J, hJ'card⟩ := Finset.exists_subset_card_eq hJ
    refine ⟨J'.image q, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.image_subset_image (Finset.subset_univ _),
        by rw [Finset.card_image_of_injective _ (oriented_path_injective hqp), hJ'card]⟩
    · simp only [Set.mem_ofPred_eq]
      intro v hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      have := hJ'J hj
      simpa using this
  have hFq : ∀ q ∈ Qf, P.real (Fq q) ≤ 2 ^ (m + 1) * (1 / 8 : ℝ) ^ m := by
    intro q _
    calc P.real (Fq q)
        ≤ ∑ S ∈ (Finset.univ.image q).powersetCard b,
            P.real {ω : Ω | ∀ v ∈ S, ω ∉ G v} := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ S ∈ (Finset.univ.image q).powersetCard b, (1 / 8 : ℝ) ^ m :=
          Finset.sum_le_sum fun S hS => hset S (Finset.mem_powersetCard.mp hS).2
      _ = (((Finset.univ.image q).card.choose b : ℕ) : ℝ) * (1 / 8 : ℝ) ^ m := by
          rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
      _ ≤ 2 ^ (m + 1) * (1 / 8 : ℝ) ^ m := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hc : (Finset.univ.image q).card ≤ m + 1 := by
            calc (Finset.univ.image q).card ≤ (Finset.univ : Finset (Fin (m + 1))).card :=
                  Finset.card_image_le
              _ = m + 1 := by simp
          have h4 : (Finset.univ.image q).card.choose b ≤ 2 ^ (m + 1) :=
            (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) hc)
          exact_mod_cast h4
  calc _ ≤ P.real (⋃ q ∈ Qf, Fq q) := measureReal_mono hcover (measure_ne_top P _)
    _ ≤ ∑ q ∈ Qf, P.real (Fq q) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Qf, (2 ^ (m + 1) * (1 / 8 : ℝ) ^ m) := Finset.sum_le_sum hFq
    _ = (Qf.card : ℝ) * (2 ^ (m + 1) * (1 / 8 : ℝ) ^ m) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ m * (2 ^ (m + 1) * (1 / 8 : ℝ) ^ m) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hQcard
    _ = 2 * (2⁻¹ : ℝ) ^ m := two_pow_mul_eighth_pow m

end LPPDifferentiability
