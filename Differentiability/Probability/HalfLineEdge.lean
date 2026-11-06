/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import Differentiability.Probability.LevelSigma
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
import Differentiability.Model.OrientedPercolationLaws
import LPP_Foundations.Model.Paths.Level
import Differentiability.Probability.AugmentedMeasurability
import LPP_Foundations.Probability.DisjointSupportEvents
import LPP_Foundations.Probability.FiniteEnvironmentLaw
import Mathlib.Probability.BorelCantelli

/-!
# The half-line edge of the top sites

Measurability of the edge `a_n(S)` with respect to the weights at levels at most
`m + n`, almost-sure nonemptiness and infinitude of the reached set, and integrability
of `a_n(Z̃₋)`.

The probability arguments use vertical paths of top sites: for starts on the antidiagonal
they are disjoint, so the events that they are open are independent, each of probability
`p₀ ^ n` with `p₀ = ν {1}`.
-/

@[expose] public section

namespace LPPDifferentiability

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- The antidiagonal half-line lies on level `0`. -/
theorem antidiagHalfLine_subset_levelSet : antidiagHalfLine ⊆ levelSet 0 :=
  fun z hz => (show z.1 + z.2 = 0 ∧ z.1 ≤ 0 from hz).1

/-- The first coordinates of the antidiagonal half-line are bounded above. -/
theorem bddAbove_fst_antidiagHalfLine : BddAbove (Prod.fst '' antidiagHalfLine) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (show z.1 + z.2 = 0 ∧ z.1 ≤ 0 from hz).2

/-- The first coordinates of the right block are bounded above. -/
theorem bddAbove_fst_antidiagRightBlock (m : ℕ) :
    BddAbove (Prod.fst '' antidiagRightBlock m) := by
  refine ⟨m, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (show z.1 + z.2 = 0 ∧ 1 ≤ z.1 ∧ z.1 ≤ m from hz).2.2

/-- The antidiagonal half-line is infinite. -/
theorem antidiagHalfLine_infinite : antidiagHalfLine.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((-(k : ℤ)), (k : ℤ)))
    (fun a b h => by simpa using congrArg Prod.snd h)
    (fun k => by
      show -(k : ℤ) + (k : ℤ) = 0 ∧ -(k : ℤ) ≤ 0
      omega)

/-- Some site reached from `S` in `n` open steps has first coordinate at least `j`. -/
private def edgeEvent (S : Set Lattice) (n : ℕ) (j : ℤ) : Set Environment :=
  {ω | ∃ v ∈ openReachSet (topSites ω) S n, j ≤ v.1}

private theorem measurableSet_edgeEvent (S : Set Lattice) (m : ℤ) (hS : S ⊆ levelSet m)
    (n : ℕ) (j : ℤ) : MeasurableSet[levelsAtMost (m + n)] (edgeEvent S n j) := by
  have hEq : edgeEvent S n j = ⋃ u : S, ⋃ v : Lattice,
      ⋃ (_ : j ≤ v.1 ∧ v.1 + v.2 = m + n), {ω | OpenReach (topSites ω) u v} := by
    ext ω
    simp only [edgeEvent, openReachSet, mem_ofPred_eq, mem_iUnion, exists_prop, Subtype.exists]
    constructor
    · rintro ⟨v, ⟨u, hu, hr, hl⟩, hj⟩
      have : u.1 + u.2 = m := hS hu
      exact ⟨u, hu, v, ⟨hj, by omega⟩, hr⟩
    · rintro ⟨u, hu, v, ⟨hj, hl⟩, hr⟩
      have : u.1 + u.2 = m := hS hu
      exact ⟨v, ⟨u, hu, hr, by omega⟩, hj⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun v =>
    MeasurableSet.iUnion fun h => measurableSet_openReach m n u v (hS u.2) h.2

theorem measurable_openEdge_levelsAtMost (S : Set Lattice) (m : ℤ) (hS : S ⊆ levelSet m)
    (n : ℕ) :
    Measurable[levelsAtMost (m + n)] (fun ω : Environment => openEdge (topSites ω) S n) := by
  have hP := measurableSet_edgeEvent S m hS n
  refine measurable_of_Ici fun j => ?_
  have hN : MeasurableSet[levelsAtMost (m + n)] (⋃ i, edgeEvent S n i) :=
    MeasurableSet.iUnion fun i => hP i
  have hB : MeasurableSet[levelsAtMost (m + n)] (⋃ b : ℤ, (edgeEvent S n (b + 1))ᶜ) :=
    MeasurableSet.iUnion fun b => (hP _).compl
  have hEq : (fun ω : Environment => openEdge (topSites ω) S n) ⁻¹' Ici j =
      ((⋃ i, edgeEvent S n i) ∩ (⋃ b : ℤ, (edgeEvent S n (b + 1))ᶜ) ∩ edgeEvent S n j) ∪
      ({_ω | j ≤ 0} ∩ ((⋃ i, edgeEvent S n i) ∩ (⋃ b : ℤ, (edgeEvent S n (b + 1))ᶜ))ᶜ) := by
    ext ω
    simp only [mem_preimage, mem_Ici, openEdge, le_maxFirst_iff, mem_union, mem_inter_iff,
      mem_iUnion, mem_compl_iff, mem_ofPred_eq, nonempty_iff_exists, bddAbove_iff_exists,
      edgeEvent]
  rw [hEq]
  exact ((hN.inter hB).inter (hP j)).union ((MeasurableSet.const (j ≤ 0)).inter (hN.inter hB).compl)

/-- The sites `u + (0,1), ..., u + (0,n)`. -/
private def vertSites (n : ℕ) (u : Lattice) : Finset Lattice :=
  Finset.univ.image fun i : Fin n => u + ((0 : ℤ), ((i : ℕ) : ℤ) + 1)

/-- All sites of the vertical path of `n` steps above `u` have weight `1`. -/
private def vertEvent (n : ℕ) (u : Lattice) : Set Environment :=
  {ω | ∀ i : Fin n, ω (u + ((0 : ℤ), ((i : ℕ) : ℤ) + 1)) = 1}

private theorem fst_of_mem_vertSites {n : ℕ} {u z : Lattice} (h : z ∈ vertSites n u) :
    z.1 = u.1 := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
  simp

private theorem measurableSet_vertEvent (n : ℕ) (u : Lattice) :
    MeasurableSet (vertEvent n u) := by
  have h : vertEvent n u = ⋂ i : Fin n,
      (fun ω : Environment => ω (u + ((0 : ℤ), ((i : ℕ) : ℤ) + 1))) ⁻¹' {1} := by
    ext ω
    simp [vertEvent]
  rw [h]
  exact MeasurableSet.iInter fun i => (measurable_pi_apply _) (measurableSet_singleton _)

private theorem vertEvent_local (n : ℕ) (u : Lattice) (ω ω' : Environment)
    (h : ∀ z ∈ vertSites n u, ω z = ω' z) : ω ∈ vertEvent n u ↔ ω' ∈ vertEvent n u := by
  simp only [vertEvent, mem_ofPred_eq]
  exact forall_congr' fun i => by rw [h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))]

private theorem real_vertEvent (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (u : Lattice) :
    (environmentLaw ν).real (vertEvent n u) = (ν.real {1}) ^ n := by
  let f : Fin n → Lattice := fun i => u + ((0 : ℤ), ((i : ℕ) : ℤ) + 1)
  have hf : Function.Injective f := by
    intro i j h
    have h2 := congrArg Prod.snd h
    simp only [f, Prod.snd_add] at h2
    exact Fin.ext (by omega)
  have hrect : MeasurableSet (Set.univ.pi fun _ : Fin n => ({1} : Set ℝ)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_singleton _
  have hpre : (fun ω : Environment => fun i => ω (f i)) ⁻¹'
      (Set.univ.pi fun _ : Fin n => ({1} : Set ℝ)) = vertEvent n u := by
    ext ω
    simp [vertEvent, f]
  rw [← hpre, ← map_measureReal_apply (measurable_finite_environment_coordinates f) hrect,
    environmentLaw_map_finite_coordinates ν f hf, measureReal_def, Measure.pi_pi,
    ENNReal.toReal_prod]
  simp [measureReal_def]

private theorem real_iInter_compl (ν : Measure ℝ) [IsProbabilityMeasure ν] (n N : ℕ) :
    (environmentLaw ν).real
        (⋂ k : Fin N, (vertEvent n ((-((k : ℕ) : ℤ)), ((k : ℕ) : ℤ)))ᶜ) =
      (1 - (ν.real {1}) ^ n) ^ N := by
  have hdisj : Pairwise fun i j : Fin N =>
      Disjoint ((vertSites n 0).map (addLeftEmbedding ((-((i : ℕ) : ℤ)), ((i : ℕ) : ℤ))))
        ((vertSites n 0).map (addLeftEmbedding ((-((j : ℕ) : ℤ)), ((j : ℕ) : ℤ)))) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hz
    obtain ⟨b, hb, hb'⟩ := Finset.mem_map.1 hz'
    have h1 := congrArg Prod.fst hb'
    have h2 := fst_of_mem_vertSites ha
    have h3 := fst_of_mem_vertSites hb
    simp only [addLeftEmbedding_apply, Prod.fst_add, Prod.fst_zero] at h1 h2 h3
    exact hij (Fin.ext (by omega))
  have h := environmentLaw_iInter_translate_compl ν (vertEvent n 0) (vertSites n 0)
    (measurableSet_vertEvent n 0) (vertEvent_local n 0) N
    (fun k : Fin N => (-((k : ℕ) : ℤ), ((k : ℕ) : ℤ))) hdisj
  have hT : ∀ u : Lattice, (environmentTranslationEquiv u) ⁻¹' vertEvent n 0 = vertEvent n u := by
    intro u
    ext ω
    simp only [mem_preimage, vertEvent, mem_ofPred_eq]
    refine forall_congr' fun i => ?_
    show ω (u + (0 + ((0 : ℤ), ((i : ℕ) : ℤ) + 1))) = 1 ↔ _
    rw [zero_add]
  simp only [hT, real_vertEvent] at h
  exact h

/-- The vertical path above a start in `A` with all weights `1` is an open path. -/
private theorem vert_mem_openReachSet (A : Set Lattice) (n : ℕ) (ω : Environment)
    {u : Lattice} (hu : u ∈ A) (h : ω ∈ vertEvent n u) :
    u + ((0 : ℤ), (n : ℤ)) ∈ openReachSet (topSites ω) A n := by
  let p : Path u (0, n) :=
    { vertex := fun k => u + ((0 : ℤ), ((k : ℕ) : ℤ))
      start := by simp
      finish := by ext <;> simp
      step := fun i => Or.inr (by ext <;> simp [add_assoc]) }
  refine ⟨u, hu, ⟨(0, n), by simp, p, fun i => ?_⟩, ?_⟩
  · have hi := i.isLt
    have h' := h ⟨i.val, by omega⟩
    show ω (u + ((0 : ℤ), (((i.succ : Fin (0 + n + 1)) : ℕ) : ℤ))) = 1
    have e : (((i.succ : Fin (0 + n + 1)) : ℕ) : ℤ) = ((i.val : ℕ) : ℤ) + 1 := by
      simp [Fin.val_succ]
    rw [e]
    exact h'
  · simp only [Prod.fst_add, Prod.snd_add]
    ring

private theorem mem_halfLine (k : ℕ) : ((-(k : ℤ)), (k : ℤ)) ∈ antidiagHalfLine := by
  show -(k : ℤ) + (k : ℤ) = 0 ∧ -(k : ℤ) ≤ 0
  exact ⟨by omega, by omega⟩

private theorem le_halfLineEdge_of_vertEvent (n : ℕ) (ω : Environment) {u : Lattice}
    (hu : u ∈ antidiagHalfLine) (h : ω ∈ vertEvent n u) : u.1 ≤ halfLineEdge ω n := by
  have hb : BddAbove (Prod.fst '' openReachSet (topSites ω) antidiagHalfLine n) := by
    refine ⟨0 + n, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact bddAbove_fst_openReachSet _ _ n 0
      (fun u hu => (show u.1 + u.2 = 0 ∧ u.1 ≤ 0 from hu).2) v hv
  calc u.1 = (u + ((0 : ℤ), (n : ℤ))).1 := by simp
    _ ≤ halfLineEdge ω n := le_maxFirst _ hb (vert_mem_openReachSet _ n ω hu h)

private theorem ae_infinite_vertical (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (n : ℕ) (A : Set Lattice) (hA : A ⊆ antidiagHalfLine)
    (hinf : A.Infinite) :
    ∀ᵐ ω ∂environmentLaw ν, {u | u ∈ A ∧ ω ∈ vertEvent n u}.Infinite := by
  let e : ℕ ↪ A := hinf.natEmbedding A
  let s : ℕ → Set Environment := fun i => vertEvent n (e i : Lattice)
  have hsm : ∀ i, MeasurableSet (s i) := fun i => measurableSet_vertEvent _ _
  have hfst : ∀ i j, i ≠ j → ((e i : A) : Lattice).1 ≠ ((e j : A) : Lattice).1 := by
    intro i j hij h
    refine hij (e.injective (Subtype.ext (Prod.ext h ?_)))
    have hi : ((e i : A) : Lattice).1 + ((e i : A) : Lattice).2 = 0 := (hA (e i).2).1
    have hj : ((e j : A) : Lattice).1 + ((e j : A) : Lattice).2 = 0 := (hA (e j).2).1
    omega
  have hind : iIndepSet s (environmentLaw ν) :=
    iIndepSet_environment_of_disjoint_supports ν s (fun i => vertSites n (e i : Lattice))
      hsm (fun i => vertEvent_local n _) fun i j hij => Finset.disjoint_left.2 fun z hz hz' =>
        hfst i j hij ((fst_of_mem_vertSites hz).symm.trans (fst_of_mem_vertSites hz'))
  have hq0 : 0 < (ν.real {1}) ^ n := pow_pos (ENNReal.toReal_pos hp₀.ne' (measure_ne_top _ _)) n
  have hc : ∀ i, environmentLaw ν (s i) = ENNReal.ofReal ((ν.real {1}) ^ n) := fun i => by
    rw [← real_vertEvent ν n (e i : Lattice), measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hsum : ∑' i, environmentLaw ν (s i) = ∞ := by
    simp_rw [hc]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (ENNReal.ofReal_pos.2 hq0).ne'
  have hlim := measure_limsup_eq_one hsm hind hsum
  have hmeas : MeasurableSet (limsup s atTop) := by
    rw [limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion]
    exact MeasurableSet.iInter fun N =>
      MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hsm i
  have hae : ∀ᵐ ω ∂environmentLaw ν, ω ∈ limsup s atTop :=
    ae_iff.2 ((prob_compl_eq_zero_iff hmeas).2 hlim)
  filter_upwards [hae] with ω hω
  have hinfI := Nat.frequently_atTop_iff_infinite.1 (mem_limsup_iff_frequently_mem.1 hω)
  have hinj : Set.InjOn (fun i : ℕ => ((e i : A) : Lattice)) {i | ω ∈ s i} :=
    fun i _ j _ h => e.injective (Subtype.ext h)
  refine (Set.Infinite.image hinj hinfI).mono ?_
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨(e i).2, hi⟩

theorem ae_openReachSet_nonempty_of_infinite (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (A : Set Lattice) (hA : A ⊆ antidiagHalfLine) (hinf : A.Infinite) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ, (openReachSet (topSites ω) A n).Nonempty := by
  have h : ∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ, {u | u ∈ A ∧ ω ∈ vertEvent n u}.Infinite :=
    ae_all_iff.2 fun n => ae_infinite_vertical ν hp₀ n A hA hinf
  filter_upwards [h] with ω hω n
  obtain ⟨u, hu, hu'⟩ := (hω n).nonempty
  exact ⟨_, vert_mem_openReachSet A n ω hu hu'⟩

theorem ae_openReachSet_halfLine_infinite (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ,
      (openReachSet (topSites ω) antidiagHalfLine n).Infinite := by
  have hinfA : antidiagHalfLine.Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((-(k : ℤ)), (k : ℤ)))
      (fun a b h => by simpa using congrArg Prod.snd h) mem_halfLine
  have h : ∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ,
      {u | u ∈ antidiagHalfLine ∧ ω ∈ vertEvent n u}.Infinite :=
    ae_all_iff.2 fun n => ae_infinite_vertical ν hp₀ n antidiagHalfLine subset_rfl hinfA
  filter_upwards [h] with ω hω n
  have hinj : Set.InjOn (fun u : Lattice => u + ((0 : ℤ), (n : ℤ)))
      {u | u ∈ antidiagHalfLine ∧ ω ∈ vertEvent n u} :=
    fun a _ b _ hab => add_right_cancel hab
  refine (Set.Infinite.image hinj (hω n)).mono ?_
  rintro _ ⟨u, ⟨hu, hu'⟩, rfl⟩
  exact vert_mem_openReachSet _ n ω hu hu'

private theorem nat_eq_tsum {Ω : Type*} (X : Ω → ℕ) (ω : Ω) :
    (X ω : ℝ≥0∞) = ∑' j : ℕ, ({w | j < X w} : Set Ω).indicator 1 ω := by
  have h : ∀ j : ℕ, ({w | j < X w} : Set Ω).indicator (1 : Ω → ℝ≥0∞) ω =
      if j < X ω then 1 else 0 := fun j => by simp [Set.indicator_apply]
  simp_rw [h]
  rw [tsum_eq_sum (s := Finset.range (X ω)) (fun j hj => by
    simp only [Finset.mem_range, not_lt] at hj
    simp [not_lt.2 hj]), Finset.sum_boole,
    Finset.filter_true_of_mem (fun j hj => Finset.mem_range.1 hj)]
  simp

theorem integrable_halfLineEdge (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (n : ℕ) :
    Integrable (fun ω => (halfLineEdge ω n : ℝ)) (environmentLaw ν) := by
  have hmeasZ : Measurable (fun ω : Environment => halfLineEdge ω n) :=
    (measurable_openEdge_levelsAtMost antidiagHalfLine 0
      (fun z hz => (show z.1 + z.2 = 0 ∧ z.1 ≤ 0 from hz).1) n).mono
      (iSup₂_le fun _ _ => (measurable_pi_apply _).comap_le) le_rfl
  obtain ⟨X, hX⟩ : ∃ X : Environment → ℕ, ∀ ω, X ω = (-(halfLineEdge ω n)).toNat :=
    ⟨_, fun _ => rfl⟩
  have hXm : Measurable X := by
    rw [show X = fun ω => (-(halfLineEdge ω n)).toNat from funext hX]
    exact (measurable_of_countable (fun z : ℤ => (-z).toNat)).comp hmeasZ
  have hq0 : 0 < ν.real {1} := ENNReal.toReal_pos hp₀.ne' (measure_ne_top _ _)
  have hqpos : 0 < (ν.real {1}) ^ n := pow_pos hq0 n
  have hqle : (ν.real {1}) ^ n ≤ 1 := pow_le_one₀ hq0.le measureReal_le_one
  have hr : ENNReal.ofReal (1 - (ν.real {1}) ^ n) < 1 := ENNReal.ofReal_lt_one.2 (by linarith)
  have htail : ∀ j : ℕ, environmentLaw ν {ω | j < X ω} ≤
      ENNReal.ofReal (1 - (ν.real {1}) ^ n) ^ (j + 1) := fun j => by
    have hsub : {ω | j < X ω} ⊆
        ⋂ k : Fin (j + 1), (vertEvent n ((-((k : ℕ) : ℤ)), ((k : ℕ) : ℤ)))ᶜ := by
      intro ω hω
      simp only [mem_iInter, mem_compl_iff]
      intro k hk
      have hle : -((k : ℕ) : ℤ) ≤ halfLineEdge ω n :=
        le_halfLineEdge_of_vertEvent n ω (mem_halfLine k) hk
      have hk' := k.isLt
      have hω' : j < X ω := hω
      have := hX ω
      omega
    calc environmentLaw ν {ω | j < X ω}
        ≤ environmentLaw ν (⋂ k : Fin (j + 1),
          (vertEvent n ((-((k : ℕ) : ℤ)), ((k : ℕ) : ℤ)))ᶜ) := measure_mono hsub
      _ = ENNReal.ofReal ((1 - (ν.real {1}) ^ n) ^ (j + 1)) := by
        rw [← ofReal_measureReal (measure_ne_top _ _), real_iInter_compl]
      _ = ENNReal.ofReal (1 - (ν.real {1}) ^ n) ^ (j + 1) :=
        ENNReal.ofReal_pow (by linarith) _
  have hset : ∀ j : ℕ, MeasurableSet {ω | j < X ω} := fun j => measurableSet_lt measurable_const hXm
  have hlint : ∫⁻ ω, (X ω : ℝ≥0∞) ∂environmentLaw ν ≠ ∞ := by
    have h1 : ∫⁻ ω, (X ω : ℝ≥0∞) ∂environmentLaw ν =
        ∑' j : ℕ, environmentLaw ν {ω | j < X ω} := by
      rw [lintegral_congr fun ω => nat_eq_tsum X ω,
        lintegral_tsum fun j => (measurable_one.indicator (hset j)).aemeasurable]
      exact tsum_congr fun j => lintegral_indicator_one (hset j)
    rw [h1]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum htail)
    rw [ENNReal.tsum_geometric_add_one]
    exact ENNReal.mul_ne_top (hr.trans ENNReal.one_lt_top).ne
      (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hr).ne')
  have hXint : Integrable (fun ω => (X ω : ℝ)) (environmentLaw ν) := by
    have := integrable_toReal_of_lintegral_ne_top (f := fun ω => (X ω : ℝ≥0∞))
      ((measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp hXm).aemeasurable hlint
    simpa using this
  have hg : Integrable (fun ω => (n : ℝ) + (X ω : ℝ)) (environmentLaw ν) :=
    (integrable_const (n : ℝ)).add hXint
  refine hg.mono' ((measurable_of_countable (Int.cast : ℤ → ℝ)).comp hmeasZ).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have h1 : halfLineEdge ω n ≤ n := halfLineEdge_le ω n
  have h2 := hX ω
  exact ⟨by exact_mod_cast (by omega : -((n : ℤ) + (X ω : ℤ)) ≤ halfLineEdge ω n),
    by exact_mod_cast (by omega : halfLineEdge ω n ≤ (n : ℤ) + (X ω : ℤ))⟩

end LPPDifferentiability
