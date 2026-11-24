/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatTop.Percolation
public import ProbabilityBasics.Probability.SupportTopCDF
import Differentiability.FinalDraft.FlatTop.OriginReach
import Differentiability.Probability.HighDensityOrientedPaths
import Differentiability.Probability.TopIndicatorLaw
import LPP_Foundations.Probability.DisjointSupportEvents
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic.Linarith

/-! The Bernoulli law, its monotonicity, and the survival threshold. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LPPDifferentiability.FinalDraft

/-- Natural-coordinate form of the origin survival event. The initial site
is allowed for every environment. -/
private theorem mem_orientedSiteSurvival_iff_natural_ray (M : ℝ) (ω : Environment) :
    ω ∈ orientedSiteSurvival M ↔
      ∃ q : ℕ → ℕ × ℕ, q 0 = 0 ∧
        (∀ n, q (n + 1) = q n + (1, 0) ∨ q (n + 1) = q n + (0, 1)) ∧
        ∀ n, q n ≠ 0 → ω ((q n).1, (q n).2) = M := by
  constructor
  · rintro ⟨γ, h0, hstep, hopen⟩
    let q (n : ℕ) : ℕ × ℕ := ((γ n).1.toNat, (γ n).2.toNat)
    have hnonneg (n : ℕ) : (0 : Lattice) ≤ γ n := by
      rw [← h0]
      exact hstep.monotone (Nat.zero_le n)
    have hcast (n : ℕ) : (((q n).1 : ℤ), ((q n).2 : ℤ)) = γ n :=
      Prod.ext (Int.toNat_of_nonneg (hnonneg n).1) (Int.toNat_of_nonneg (hnonneg n).2)
    refine ⟨q, by simp [q, h0], ?_, ?_⟩
    · intro n
      have hconvert (a b : ℕ) (h : γ (n + 1) = γ n + ((a : ℤ), (b : ℤ))) :
          q (n + 1) = q n + (a, b) := by
        rw [← hcast n, ← hcast (n + 1)] at h
        apply Prod.ext
        · have h₁ := congrArg Prod.fst h
          simp only [Prod.fst_add] at h₁ ⊢
          omega
        · have h₂ := congrArg Prod.snd h
          simp only [Prod.snd_add] at h₂ ⊢
          omega
      exact (hstep n).imp (hconvert 1 0) (hconvert 0 1)
    · intro n hn
      rw [hcast n]
      cases n with
      | zero => exact (hn (by simp [q, h0])).elim
      | succ n => exact hopen n
  · rintro ⟨q, h0, hstep, hopen⟩
    let γ (n : ℕ) : Lattice := ((q n).1, (q n).2)
    have hγ0 : γ 0 = 0 := by simp [γ, h0]
    have hγstep : IsUpRightRay γ := by
      intro n
      rcases hstep n with h | h
      · left
        apply Prod.ext <;> simp only [γ, h, Prod.fst_add, Prod.snd_add, Nat.cast_add,
          Nat.cast_one, Nat.cast_zero]
      · right
        apply Prod.ext <;> simp only [γ, h, Prod.fst_add, Prod.snd_add, Nat.cast_add,
          Nat.cast_one, Nat.cast_zero]
    refine ⟨γ, hγ0, hγstep, fun n => hopen (n + 1) ?_⟩
    intro h
    have hlev := hγstep.level (n + 1)
    have hγ : γ (n + 1) = 0 := by simp [γ, h]
    rw [hγ0, hγ] at hlev
    simp at hlev
    omega

/-- Survival is measurable because all finite open-prefix events are measurable. -/
theorem measurableSet_orientedSiteSurvival (M : ℝ) : MeasurableSet (orientedSiteSurvival M) := by
  classical
  let G (x : ℕ × ℕ) : Set Environment := if x = 0 then univ else
    {ω | ω ((x.1 : ℤ), (x.2 : ℤ)) = M}
  have hG (x : ℕ × ℕ) : MeasurableSet (G x) := by
    dsimp only [G]
    split_ifs
    · exact MeasurableSet.univ
    · exact (measurable_environment_eval _) (measurableSet_singleton _)
  have hEq : orientedSiteSurvival M =
      {ω : Environment | ∃ q : ℕ → ℕ × ℕ, q 0 = (0, 0) ∧
        (∀ i, q (i + 1) = q i + (1, 0) ∨ q (i + 1) = q i + (0, 1)) ∧
        ∀ i, ω ∈ G (q i)} := by
    ext ω
    rw [mem_orientedSiteSurvival_iff_natural_ray]
    constructor
    · rintro ⟨q, hq0, hstep, hgood⟩
      refine ⟨q, hq0, hstep, fun n => ?_⟩
      by_cases hz : q n = 0
      · simp [G, hz]
      · simpa [G, hz] using hgood n hz
    · rintro ⟨q, hq0, hstep, hgood⟩
      exact ⟨q, hq0, hstep, fun n hn => by simpa [G, hn] using hgood n⟩
  rw [hEq]
  exact measurableSet_exists_infinite_good_oriented_path G hG

/-- The positive-survival side of the Bernoulli threshold is nonempty below
one, by the site Peierls estimate. -/
private theorem exists_bernoulli_survival_below_one :
    ∃ p : unitInterval, (p : ℝ) < 1 ∧
      0 < environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) (orientedSiteSurvival 1) := by
  classical
  obtain ⟨ζ, hζ, hζ1, hcut⟩ := exists_high_density_oriented_path_cutoff 0
  let p : unitInterval := ⟨1 - ζ, ⟨by linarith, by linarith⟩⟩
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  let φ (x : ℕ × ℕ) : Lattice := ((x.1 : ℤ), (x.2 : ℤ))
  have hφ : Function.Injective φ := by
    intro x y h
    exact Prod.ext (by simpa [φ] using congrArg Prod.fst h)
      (by simpa [φ] using congrArg Prod.snd h)
  let G (x : ℕ × ℕ) : Set Environment := {ω | ω (φ x) = 1}
  have hG (x : ℕ × ℕ) : MeasurableSet (G x) :=
    (measurable_environment_eval _) (measurableSet_singleton _)
  have hGm (x : ℕ × ℕ) : (environmentLaw ν).real (G x)ᶜ ≤ ζ := by
    have h1 : (environmentLaw ν).real (G x) = (p : ℝ) := by
      change (environmentLaw ν).real ((fun ω : Environment => ω (φ x)) ⁻¹' ({1} : Set ℝ)) =
        (p : ℝ)
      rw [← map_measureReal_apply (measurable_environment_eval _) (measurableSet_singleton _),
        environmentLaw_map_eval]
      exact bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton _)
        (by simp) (by simp)
    rw [probReal_compl_eq_one_sub (hG x), h1]
    change 1 - (1 - ζ) ≤ ζ
    linarith
  have hindep (T : Finset (ℕ × ℕ)) :
      iIndepSet (fun v : {u // u ∈ T} => G v.1) (environmentLaw ν) := by
    refine iIndepSet_environment_of_disjoint_supports ν _ (fun v => {φ v.1}) (fun v => hG _)
      (fun v ω ω' h => ?_) (fun v w hvw => ?_)
    · change ω (φ v.1) = 1 ↔ ω' (φ v.1) = 1
      rw [h _ (Finset.mem_singleton_self _)]
    · exact Finset.disjoint_singleton.mpr (fun he => hvw (Subtype.ext (hφ he)))
  obtain ⟨_, hsurv⟩ := hcut (environmentLaw ν) G hG hGm (fun T _ => hindep T)
  have hsub :
      {ω : Environment | ∃ q : ℕ → ℕ × ℕ, q 0 = (0, 0) ∧
        (∀ i, q (i + 1) = q i + (1, 0) ∨ q (i + 1) = q i + (0, 1)) ∧
        ∀ i, ω ∈ G (q i)} ⊆ orientedSiteSurvival 1 := by
    intro ω hω
    obtain ⟨q, h0, hstep, hgood⟩ := hω
    exact (mem_orientedSiteSurvival_iff_natural_ray 1 ω).mpr
      ⟨q, h0, hstep, fun n _ => hgood n⟩
  have hpositive : 0 < environmentLaw ν (orientedSiteSurvival 1) :=
    lt_of_lt_of_le (ENNReal.toReal_pos_iff.mp hsurv).1 (measure_mono hsub)
  exact ⟨p, by change 1 - ζ < 1; linarith, hpositive⟩

/-- The critical density lies strictly between zero and one. -/
theorem orientedSiteCriticalDensity_mem_Ioo : orientedSiteCriticalDensity ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨p, hp₁, hsurv⟩ := exists_bernoulli_survival_below_one
  let S : Set ℝ := {q | ∃ r : unitInterval, (r : ℝ) = q ∧
    0 < environmentLaw (bernoulliMeasure (1 : ℝ) 0 r) (orientedSiteSurvival 1)}
  have hpS : (p : ℝ) ∈ S := ⟨p, rfl, hsurv⟩
  have hlower : (1 / 4 : ℝ) ∈ lowerBounds S := by
    rintro q ⟨r, hr, hrSurvival⟩
    rw [← hr]
    apply le_of_not_gt
    intro hlt
    rw [measure_orientedSiteSurvival_eq_zero_of_lt_one_quarter r hlt] at hrSurvival
    exact (lt_irrefl _ hrSurvival).elim
  have hlo : (1 / 4 : ℝ) ≤ sInf S :=
    le_csInf (show S.Nonempty from ⟨(p : ℝ), hpS⟩) (fun r hr => hlower hr)
  have hhi : sInf S ≤ (p : ℝ) := csInf_le ⟨1 / 4, hlower⟩ hpS
  exact ⟨lt_of_lt_of_le (by norm_num) hlo, hhi.trans_lt hp₁⟩

/-- The survival probability for a finite support top is the Bernoulli survival probability
at the mass of its atom. -/
theorem measure_orientedSiteSurvival_eq_bernoulli (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ) (hM : (M : EReal) = supportTop μ) :
    environmentLaw μ (orientedSiteSurvival M) =
      environmentLaw (bernoulliMeasure (1 : ℝ) 0 ⟨μ.real {M}, by simp⟩)
        (orientedSiteSurvival 1) := by
  have hAtom : supportTopAtom μ = {M} := by
    ext x
    change (x : EReal) = supportTop μ ↔ x ∈ ({M} : Set ℝ)
    rw [← hM, EReal.coe_eq_coe_iff, mem_singleton_iff]
  have hpre : topWeightIndicatorField μ ⁻¹' orientedSiteSurvival 1 = orientedSiteSurvival M := by
    ext ω
    change (∃ γ : ℕ → Lattice, γ 0 = 0 ∧ IsUpRightRay γ ∧
      ∀ n, topWeightIndicator μ (ω (γ (n + 1))) = 1) ↔
        ∃ γ : ℕ → Lattice, γ 0 = 0 ∧ IsUpRightRay γ ∧ ∀ n, ω (γ (n + 1)) = M
    simp [topWeightIndicator, ← hM, EReal.coe_eq_coe_iff]
  rw [← hpre, ← Measure.map_apply (measurable_source_top_indicator_environment μ)
    (measurableSet_orientedSiteSurvival 1), source_top_indicator_environmentLaw_map]
  simp only [environmentLaw, (source_top_indicator_hasLaw μ).map_eq, hAtom]

/-- Thresholding one uniform value gives the Bernoulli site law. -/
private theorem uniformThreshold_hasLaw (p : unitInterval) :
    HasLaw (fun u : unitInterval => if u ≤ p then (1 : ℝ) else 0)
      (bernoulliMeasure (1 : ℝ) 0 p) (volume : Measure unitInterval) := by
  have hprob : (volume : Measure unitInterval).real (Iic p) = (p : ℝ) := by
    rw [Measure.real_def, unitInterval.volume_Iic, ENNReal.toReal_ofReal p.property.1]
  have h := hasLaw_indicator_bernoulliMeasure (1 : ℝ)
    (P := (volume : Measure unitInterval)) (s := Iic p) measurableSet_Iic.nullMeasurableSet
  have hparam : (⟨(volume : Measure unitInterval).real (Iic p), by simp⟩ : unitInterval) = p :=
    Subtype.ext hprob
  rw [hparam] at h
  have heq : (Iic p).indicator (fun _ => (1 : ℝ)) =
      (fun u : unitInterval => if u ≤ p then 1 else 0) := by
    funext u
    by_cases hu : u ≤ p <;> simp [hu]
  rwa [heq] at h

/-- Survival probability in the Bernoulli environment is increasing in the
density, by using one uniform value per site for both fields. -/
theorem orientedSiteSurvival_bernoulli_mono :
    Monotone (fun p : unitInterval =>
      environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) (orientedSiteSurvival 1)) := by
  let U := Measure.infinitePi (fun _ : Lattice => (volume : Measure unitInterval))
  let T (p : unitInterval) (ω : Lattice → unitInterval) : Environment :=
    fun z => if ω z ≤ p then 1 else 0
  have hG (p : unitInterval) :
      Measurable (fun u : unitInterval => if u ≤ p then (1 : ℝ) else 0) :=
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hT (p : unitInterval) : Measurable (T p) :=
    Measurable.of_eval fun z => (hG p).comp (measurable_pi_apply z)
  have hLaw (p : unitInterval) :
      U.map (T p) = environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) := by
    change (Measure.infinitePi (fun _ : Lattice => (volume : Measure unitInterval))).map (T p) = _
    rw [show (Measure.infinitePi (fun _ : Lattice => (volume : Measure unitInterval))).map (T p) =
      Measure.infinitePi (fun _ : Lattice => (volume : Measure unitInterval).map
        (fun u : unitInterval => if u ≤ p then (1 : ℝ) else 0)) from
      Measure.infinitePi_map_pi _ (fun _ => hG p)]
    simp only [environmentLaw, (uniformThreshold_hasLaw p).map_eq]
  intro p q hpq
  change environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) (orientedSiteSurvival 1) ≤
    environmentLaw (bernoulliMeasure (1 : ℝ) 0 q) (orientedSiteSurvival 1)
  rw [← hLaw p, ← hLaw q, Measure.map_apply (hT p) (measurableSet_orientedSiteSurvival 1),
    Measure.map_apply (hT q) (measurableSet_orientedSiteSurvival 1)]
  apply measure_mono
  intro ω hω
  obtain ⟨γ, hγ0, hγstep, hγopen⟩ := hω
  refine ⟨γ, hγ0, hγstep, fun n => ?_⟩
  have hopenP : ω (γ (n + 1)) ≤ p := by
    have h := hγopen n
    change (if ω (γ (n + 1)) ≤ p then (1 : ℝ) else 0) = 1 at h
    by_contra! hn
    simp [not_le.mpr hn] at h
  exact ite_eq_left (hopenP.trans hpq)

/-- The origin survives with positive probability when the actual top atom
is above the critical density. -/
theorem measure_orientedSiteSurvival_pos_of_criticalDensity_lt
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℝ) (hM : (M : EReal) = supportTop μ)
    (h : orientedSiteCriticalDensity < μ.real {M}) :
    0 < environmentLaw μ (orientedSiteSurvival M) := by
  let S : Set ℝ := {q | ∃ p : unitInterval, (p : ℝ) = q ∧
    0 < environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) (orientedSiteSurvival 1)}
  obtain ⟨q, _, hq⟩ := exists_bernoulli_survival_below_one
  have hne : S.Nonempty := ⟨q, q, rfl, hq⟩
  obtain ⟨r, ⟨p, hp, hpositive⟩, hlt⟩ :=
    exists_lt_of_csInf_lt hne (show sInf S < μ.real {M} from h)
  let q' : unitInterval := ⟨μ.real {M}, by simp⟩
  have hpq : p ≤ q' := by
    change (p : ℝ) ≤ μ.real {M}
    exact hp.trans_le hlt.le
  rw [measure_orientedSiteSurvival_eq_bernoulli μ M hM]
  exact lt_of_lt_of_le hpositive (orientedSiteSurvival_bernoulli_mono hpq)

/-- Below the critical density the origin survival probability is zero. -/
theorem measure_orientedSiteSurvival_eq_zero_of_lt_criticalDensity
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℝ) (hM : (M : EReal) = supportTop μ)
    (h : μ.real {M} < orientedSiteCriticalDensity) :
    environmentLaw μ (orientedSiteSurvival M) = 0 := by
  rw [measure_orientedSiteSurvival_eq_bernoulli μ M hM]
  apply le_antisymm _ bot_le
  apply le_of_not_gt
  intro hsurv
  have hle : orientedSiteCriticalDensity ≤ μ.real {M} := by
    apply csInf_le (show BddBelow {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧
      0 < environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) (orientedSiteSurvival 1)} from
      ⟨0, by rintro q ⟨p, rfl, _⟩; exact p.property.1⟩)
    exact ⟨⟨μ.real {M}, by simp⟩, rfl, hsurv⟩
  exact h.not_ge hle

end LPPDifferentiability.FinalDraft
