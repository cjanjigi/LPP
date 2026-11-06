/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TiltWitnessSelection
public import Differentiability.Probability.TiltWitnessBoost
public import Differentiability.Probability.TiltStripBadSites
public import Differentiability.Probability.TiltStripTopSites
public import Differentiability.Probability.MaximumKernelGoodSet
public import Differentiability.Probability.MaximumFiberIntegration
public import Differentiability.Probability.MaximumKernelRN
public import Differentiability.Analysis.CubicTiltScaling
import Mathlib.Tactic

/-!
# The change of measure at cubic length

The proof of Lemma 4.2 of the differentiability preprint, up to its final limit,
which needs Proposition 3.4. For `n = ⌈s³⌉`, the crossing event `E(s, n)` (a path
`x_{0:n}` from a start on level `0`, every vertex in the strip `|r| ≤ 8s`,
weight above `G0 n - K s`) satisfies

`P(E) ≤ P(Uᶜ) + P(Vᶜ) + exp(3δ²|R|/2) √P(calE) + 4/λ`,

where `calE(s, n)` is the event of Proposition 3.4 with `σ = +`, `R = 8`,
`ε = 1`: some strip path `x_{0:n}` has `f_+(x_n - x_0) - W(x) < -s`. Hence
`P(E(s, ⌈s³⌉)) ≤ err(s) + C √P(calE(s, ⌈s³⌉))` with `err → 0`.

`G0`, `dl`, `dr` stand for `g(ξ)` and the two one-sided slopes and are
arbitrary reals. `Gtop` is the value at `ξ = (a, 1 - a)` of the top-indicator
shape, identified by the limit of its normalized means; the off-flat condition
is `Gtop < 1`.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace LPPDifferentiability

private theorem measurableSet_level_zero_path_event (n : ℕ)
    (P : (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop)
    (Q : (u : Lattice) → (e : ℕ × ℕ) → Path u e → Environment → Prop)
    (hQ : ∀ u e q, MeasurableSet {ω | Q u e q ω}) :
    MeasurableSet {ω : Environment | ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ,
      e.1 + e.2 = n ∧ ∃ q : Path u e, P u e q ∧ Q u e q ω} := by
  have hEq : {ω : Environment | ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ,
      e.1 + e.2 = n ∧ ∃ q : Path u e, P u e q ∧ Q u e q ω} =
      ⋃ u : Lattice, ⋃ e : ℕ × ℕ, ⋃ q : Path u e,
        {_ω : Environment | u.1 + u.2 = 0 ∧ e.1 + e.2 = n ∧ P u e q} ∩
          {ω | Q u e q ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨u, hu, e, he, q, hP, hQ'⟩
      exact ⟨u, e, q, ⟨hu, he, hP⟩, hQ'⟩
    · rintro ⟨u, e, q, ⟨hu, he, hP⟩, hQ'⟩
      exact ⟨u, hu, e, he, q, hP, hQ'⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun e =>
    MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter (hQ u e q)

private theorem add_mul_le_add_mul {x y d e q C : ℝ} (he : e ≤ C) (hq : 0 ≤ q) :
    x + y + e * q + d ≤ x + y + d + C * q := by
  have h := mul_le_mul_of_nonneg_right he hq
  linarith only [h]

/-- The finite-`s` change-of-measure inequality from the proof of Lemma 4.2 of the
differentiability preprint, without the final limit. `α`, `c'` and the good set
`I` come from part (ii) of Lemma 4.1 with `β = 16^(-1/φ)`; `δ`, `λ`, `R` are as
in the paper. The
hypothesis `_htop` identifies `Gtop` as the top-indicator shape at `ξ`; the
finite inequality itself uses only `Gtop < 1`. -/
theorem tilt_change_of_measure_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) (G0 dl dr Gtop : ℝ)
    (_htop : Tendsto (fun m : ℕ => (∫ ω : Environment, lastPassage (fun z =>
      if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
        0 (⌊(m : ℝ) * a⌋₊, ⌊(m : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) / (m : ℝ))
      atTop (𝓝 Gtop))
    (hgap : Gtop < 1) :
    let M : EReal := sSup ((fun t : ℝ => (t : EReal)) '' μ.support)
    let K : ℝ := 100 * (1 + |dl| + |dr|)
    let φ : ℝ := (1 - Gtop) / 4
    let η : ℝ := (K + 16 * |dr| + 1) / 2
    ∃ α ∈ Ioo (0 : ℝ) (1 / 2), ∃ c' > 0,
      let I : Set ℝ := {t : ℝ | (t : EReal) < M ∧ μ.real (Iic t) ≤ 1 - α ∧
        c' ≤ sInf {r : ℝ | μ.real (Iic t) + α / 2 ≤ μ.real (Iic r)} - t}
      MeasurableSet I ∧
      μ.real ((I ∪ {t : ℝ | (t : EReal) = M})ᶜ) ≤ Real.rpow 16 (-1 / φ) ∧
      ∀ s : ℝ, 1 ≤ s →
        let n : ℕ := Nat.ceil (s ^ 3)
        let δ : ℝ := 8 * η * s / (α * φ * c' * (n : ℝ))
        let lam : ℝ := (Nat.ceil (φ * (n : ℝ)) : ℝ) * δ * α / 2
        let R : Finset Lattice := (Finset.Icc (0 : ℤ) (n : ℤ)).biUnion (fun k => (Finset.Icc
          (Int.ceil (a * (k : ℝ) - 8 * s)) (Int.floor (a * (k : ℝ) + 8 * s))).image
            (fun i => (i, k - i)))
        δ < 1 →
        (environmentLaw μ).real {ω : Environment | ∃ u : Lattice, u.1 + u.2 = 0 ∧
            ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
              (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
              G0 * (n : ℝ) - K * s < pathWeight ω q} ≤
          (environmentLaw μ).real {ω : Environment |
            ∃ u : Lattice, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
              (∀ j, 0 ≤ (q.2.vertex j).1 + (q.2.vertex j).2 ∧
                (q.2.vertex j).1 + (q.2.vertex j).2 ≤ (n : ℤ) ∧
                |(1 - a) * ((q.2.vertex j).1 : ℝ) - a * ((q.2.vertex j).2 : ℝ)| ≤ 8 * s) ∧
              φ * (n : ℝ) < ((@Finset.filter Lattice
                (fun z => ω z ∈ (I ∪ {t : ℝ | (t : EReal) = M})ᶜ)
                (Classical.decPred _) q.2.collectedSites).card : ℝ)} +
          (environmentLaw μ).real {ω : Environment | ∃ u : Lattice,
            ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
              (∀ j, 0 ≤ (q.2.vertex j).1 + (q.2.vertex j).2 ∧
                (q.2.vertex j).1 + (q.2.vertex j).2 ≤ (n : ℤ) ∧
                |(1 - a) * ((q.2.vertex j).1 : ℝ) - a * ((q.2.vertex j).2 : ℝ)| ≤ 8 * s) ∧
              (1 - 2 * φ) * (n : ℝ) < ((q.2.collectedSites.filter
                (fun z => (ω z : EReal) = M)).card : ℝ)} +
          Real.exp ((3 / 2 : ℝ) * δ ^ 2 * R.card) *
            Real.sqrt ((environmentLaw μ).real {ω : Environment | ∃ u : Lattice,
              u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
                (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
                G0 * (((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) +
                    ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) +
                  dr * ((1 - a) * ((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) -
                    a * ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) -
                  pathWeight ω q < -s}) +
          4 / lam := by
  intro M K φ η
  have hφ : 0 < φ := by
    change 0 < (1 - Gtop) / 4
    linarith only [hgap]
  have hη : 0 < η := by
    change 0 < (100 * (1 + |dl| + |dr|) + 16 * |dr| + 1) / 2
    positivity
  have hβ : 0 < Real.rpow 16 (-1 / φ) := Real.rpow_pos_of_pos (by norm_num) _
  have hkernel := maximum_kernel_good_set μ hβ
  dsimp only at hkernel
  obtain ⟨α, hα, c', hc', hImeas, hmass, -⟩ := hkernel
  refine ⟨α, hα, c', hc', ?_⟩
  intro I
  refine ⟨hImeas, hmass, ?_⟩
  intro s hs n δ lam R hδ1
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hn1 : 1 ≤ n := (cubic_length_ceil_bounds s hs).1
  have hα1 : α ∈ Ioo (0 : ℝ) 1 := ⟨hα.1, hα.2.trans (by norm_num)⟩
  have hδpos : 0 < δ := (cubic_tilt_delta_bounds α φ c' η s hα.1 hφ hc' hη hs).1
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδpos, hδ1⟩
  have hδI : δ ∈ Icc (0 : ℝ) 1 := ⟨hδpos.le, hδ1.le⟩
  have hlamlow : 4 * η * s / c' ≤ lam :=
    cubic_tilt_binomial_mean_lower_bound α φ c' η s hα.1 hφ hc' hη hs
  have hlampos : 0 < lam :=
    lt_of_lt_of_le (div_pos (mul_pos (mul_pos (by norm_num) hη) hspos) hc') hlamlow
  have hmean : (K + 16 * |dr| + 1) * s ≤ c' * lam / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hlamlow hc'.le
    have h2 : c' * (4 * η * s / c') = 4 * η * s := by field_simp [hc'.ne']
    have h3 : K + 16 * |dr| + 1 = 2 * η := by
      change K + 16 * |dr| + 1 = 2 * ((K + 16 * |dr| + 1) / 2)
      ring
    rw [h3]
    linarith only [h1, h2]
  -- The four events and the good part `E° = E ∩ U ∩ V`.
  set Ev : Set Environment := {ω : Environment | ∃ u : Lattice, u.1 + u.2 = 0 ∧
      ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
        G0 * (n : ℝ) - K * s < pathWeight ω q}
  set A : Set ℝ := (I ∪ {t : ℝ | (t : EReal) = M})ᶜ
  set Ub : Set Environment := {ω : Environment |
      ∃ u : Lattice, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        (∀ j, 0 ≤ (q.2.vertex j).1 + (q.2.vertex j).2 ∧
          (q.2.vertex j).1 + (q.2.vertex j).2 ≤ (n : ℤ) ∧
          |(1 - a) * ((q.2.vertex j).1 : ℝ) - a * ((q.2.vertex j).2 : ℝ)| ≤ 8 * s) ∧
        φ * (n : ℝ) < ((@Finset.filter Lattice (fun z => ω z ∈ A)
          (Classical.decPred _) q.2.collectedSites).card : ℝ)}
  set Vb : Set Environment := {ω : Environment | ∃ u : Lattice,
      ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        (∀ j, 0 ≤ (q.2.vertex j).1 + (q.2.vertex j).2 ∧
          (q.2.vertex j).1 + (q.2.vertex j).2 ≤ (n : ℤ) ∧
          |(1 - a) * ((q.2.vertex j).1 : ℝ) - a * ((q.2.vertex j).2 : ℝ)| ≤ 8 * s) ∧
        (1 - 2 * φ) * (n : ℝ) < ((q.2.collectedSites.filter
          (fun z => (ω z : EReal) = M)).card : ℝ)}
  set Fe : Set Environment := {ω : Environment | ∃ u : Lattice,
      u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
        G0 * (((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) +
            ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) +
          dr * ((1 - a) * ((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) -
            a * ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) -
          pathWeight ω q < -s}
  have hAmeas : MeasurableSet A :=
    (hImeas.union ((measurableSet_singleton M).preimage
      continuous_coe_real_ereal.measurable)).compl
  have hEv : MeasurableSet Ev := measurableSet_level_zero_path_event n
    (fun _ _ q => ∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s)
    (fun _ _ q ω => G0 * (n : ℝ) - K * s < pathWeight ω q)
    (fun _ _ q => measurableSet_lt measurable_const (measurable_pathWeight q))
  have hUb : MeasurableSet Ub := measurableSet_exists_closed_strip_bad_sites A hAmeas a s φ n
  have hVb : MeasurableSet Vb := measurableSet_closed_strip_top_sites μ a s φ n
  have hFe : MeasurableSet Fe := measurableSet_level_zero_path_event n
    (fun _ _ q => ∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s)
    (fun u e q ω => G0 * (((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) +
            ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) +
          dr * ((1 - a) * ((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) -
            a * ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) -
          pathWeight ω q < -s)
    (fun _ _ q => measurableSet_lt (measurable_const.sub (measurable_pathWeight q))
      measurable_const)
  set E0 : Set Environment := Ev ∩ Ubᶜ ∩ Vbᶜ
  have hE0 : MeasurableSet E0 := (hEv.inter hUb.compl).inter hVb.compl
  -- Split the event: `P(E) ≤ P(E°) + P(Uᶜ) + P(Vᶜ)`.
  have hsplit : (environmentLaw μ).real Ev ≤
      (environmentLaw μ).real E0 + (environmentLaw μ).real Ub +
        (environmentLaw μ).real Vb := by
    have hsub : Ev ⊆ E0 ∪ Ub ∪ Vb := by
      intro ω hω
      by_cases hu : ω ∈ Ub
      · exact Or.inl (Or.inr hu)
      · by_cases hv : ω ∈ Vb
        · exact Or.inr hv
        · exact Or.inl (Or.inl ⟨⟨hω, hu⟩, hv⟩)
    have hu1 := measureReal_union_le (μ := environmentLaw μ) (E0 ∪ Ub) Vb
    have hu2 := measureReal_union_le (μ := environmentLaw μ) E0 Ub
    have hmono := measureReal_mono (μ := environmentLaw μ) hsub
    linarith only [hu1, hu2, hmono]
  -- Fiber by fiber: on `E°` the boost fails with
  -- conditional probability at most `4/λ`.
  have hfiber : ∀ w ∈ E0,
      ((environmentLaw μ).prod (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))).real
        {r : Environment × (Lattice → Bool) | ((w, r.1), r.2) ∈
          {p : (Environment × Environment) × (Lattice → Bool) |
            (fun v => if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v)
              else p.1.1 v) ∉ Fe}} ≤ 4 / lam := by
    rintro w ⟨⟨hwE, hwU⟩, hwV⟩
    obtain ⟨u, hu, ⟨e1, e2⟩, he, q, hstrip, hweight⟩ := hwE
    change e1 + e2 = n at he
    obtain rfl : e2 = n - e1 := by omega
    have he1 : e1 < n + 1 := by omega
    let Q : Σ i : Fin (n + 1), Path u (i.val, n - i.val) := ⟨⟨e1, he1⟩, q⟩
    have hclosed : ∀ j, 0 ≤ (Q.2.vertex j).1 + (Q.2.vertex j).2 ∧
        (Q.2.vertex j).1 + (Q.2.vertex j).2 ≤ (n : ℤ) ∧
        |(1 - a) * ((Q.2.vertex j).1 : ℝ) - a * ((Q.2.vertex j).2 : ℝ)| ≤ 8 * s :=
      fun j => ⟨(Path.level_zero_closed_strip_levels q hu he j).1,
        (Path.level_zero_closed_strip_levels q hu he j).2, hstrip j⟩
    have hAq : ((@Finset.filter Lattice (fun z => w z ∈ (I ∪ {t : ℝ | (t : EReal) = M})ᶜ)
        (Classical.decPred _) q.collectedSites).card : ℝ) ≤ φ * (n : ℝ) := by
      by_contra h
      exact hwU ⟨u, Q, hclosed, lt_of_not_ge h⟩
    have hTq : ((@Finset.filter Lattice (fun z => w z ∈ {t : ℝ | (t : EReal) = M})
        (Classical.decPred _) q.collectedSites).card : ℝ) ≤ (1 - 2 * φ) * (n : ℝ) := by
      by_contra h
      apply hwV
      refine ⟨u, Q, hclosed, ?_⟩
      have heq : (@Finset.filter Lattice (fun z => w z ∈ {t : ℝ | (t : EReal) = M})
          (Classical.decPred _) q.collectedSites) =
          q.collectedSites.filter (fun z => (w z : EReal) = M) := by
        ext z
        rw [@Finset.mem_filter Lattice (fun z => w z ∈ {t : ℝ | (t : EReal) = M})
          (Classical.decPred _), Finset.mem_filter]
        rfl
      change (1 - 2 * φ) * (n : ℝ) <
        ((q.collectedSites.filter (fun z => (w z : EReal) = M)).card : ℝ)
      rw [← heq]
      exact lt_of_not_ge h
    obtain ⟨S, hSq, hScard, hSI⟩ :=
      Path.exists_good_collected_subset q he w I {t : ℝ | (t : EReal) = M} φ hAq hTq
    have hSI' : ∀ z ∈ S, (w z : EReal) < M ∧ μ.real (Iic (w z)) ≤ 1 - α ∧
        c' ≤ sInf {r : ℝ | μ.real (Iic (w z)) + α / 2 ≤ μ.real (Iic r)} - w z := hSI
    have hSR : S ⊆ R :=
      hSq.trans (Path.level_zero_strip_collectedSites_subset_region a s q hu he hstrip)
    have hSne : S.Nonempty := by
      rw [← Finset.card_pos, hScard]
      exact Nat.ceil_pos.2 (mul_pos hφ (Nat.cast_pos.2 hn1))
    have hmeanS : (K + 16 * |dr| + 1) * s ≤ c' * ((S.card : ℝ) * δ * α / 2) / 2 := by
      rw [hScard]
      exact hmean
    have hb := tilt_fixed_witness_boost_failure_le μ hδ hα1 hc' a s G0 dr K n R S w
      q hu he hstrip hweight hSq hSR hSne (fun v hv => (hSI' v hv).2.1)
      (fun v hv => (hSI' v hv).2.2) hmeanS
    rw [hScard] at hb
    exact hb
  -- Split under the joint law, then change measure.
  have hT := measurable_maximum_modification R
  have hEbad : MeasurableSet {p : (Environment × Environment) × (Lattice → Bool) |
      (fun v => if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v)
        else p.1.1 v) ∉ Fe} := hT hFe.compl
  have hgood := maximum_kernel_map_event_bound μ hδI R hFe
  rw [map_measureReal_apply hT hFe] at hgood
  have hbad := maximum_modification_joint_inter_real_le_of_fiber_bound μ hδI hE0 hEbad
    (div_nonneg (by norm_num) hlampos.le) hfiber
  have hE0joint := maximum_modification_original_real μ hδI hE0
  have hcover : {p : (Environment × Environment) × (Lattice → Bool) | p.1.1 ∈ E0} ⊆
      ((fun p : (Environment × Environment) × (Lattice → Bool) =>
          fun v => if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v) else p.1.1 v) ⁻¹' Fe) ∪
        {p | p.1.1 ∈ E0 ∧ p ∈ {p : (Environment × Environment) × (Lattice → Bool) |
          (fun v => if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v)
            else p.1.1 v) ∉ Fe}} := by
    intro p hp
    by_cases h : (fun v => if v ∈ R ∧ p.2 v = true then max (p.1.1 v) (p.1.2 v)
        else p.1.1 v) ∈ Fe
    · exact Or.inl h
    · exact Or.inr ⟨hp, h⟩
  have : IsProbabilityMeasure (((environmentLaw μ).prod (environmentLaw μ)).prod
      (Measure.infinitePi (fun _ : Lattice =>
        ENNReal.ofReal (1 - δ) • Measure.dirac false +
          ENNReal.ofReal δ • Measure.dirac true))) :=
    maximum_modification_joint_is_probability μ hδI
  have hE0bound : (environmentLaw μ).real E0 ≤
      Real.exp ((3 / 2 : ℝ) * δ ^ 2 * R.card) *
        Real.sqrt ((environmentLaw μ).real Fe) + 4 / lam := by
    rw [← hE0joint]
    exact (measureReal_mono hcover).trans ((measureReal_union_le _ _).trans
      (add_le_add hgood hbad))
  linarith only [hsplit, hE0bound]

/-- The corollary of the change of measure at cubic length: for all large `s`,
`P(E(s, ⌈s³⌉)) ≤ err(s) + C √P(calE(s, ⌈s³⌉))`, where `err(s)` is the sum of
`P(Uᶜ)`, `P(Vᶜ)` and `4/λ` and tends to zero by the strip-rarity results and the
scaling of `λ`, and `C = exp(3264 η²/(α²φ²c'²))`. The direction conditions
`0 < a < 1` are used to identify `Gtop` with the top-indicator shape at `ξ`. -/
theorem tilt_change_of_measure_eventually_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (G0 dl dr Gtop : ℝ)
    (htop : Tendsto (fun m : ℕ => (∫ ω : Environment, lastPassage (fun z =>
      if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
        0 (⌊(m : ℝ) * a⌋₊, ⌊(m : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) / (m : ℝ))
      atTop (𝓝 Gtop))
    (hgap : Gtop < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ err : ℝ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ s : ℝ in atTop,
        (environmentLaw μ).real {ω : Environment | ∃ u : Lattice, u.1 + u.2 = 0 ∧
            ∃ e : ℕ × ℕ, e.1 + e.2 = Nat.ceil (s ^ 3) ∧ ∃ q : Path u e,
              (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
              G0 * (Nat.ceil (s ^ 3) : ℝ) - 100 * (1 + |dl| + |dr|) * s <
                pathWeight ω q} ≤
          err s + C * Real.sqrt ((environmentLaw μ).real {ω : Environment | ∃ u : Lattice,
            u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = Nat.ceil (s ^ 3) ∧ ∃ q : Path u e,
              (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) ∧
              G0 * (((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) +
                  ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) +
                dr * ((1 - a) * ((q.vertex (Fin.last (e.1 + e.2)) - u).1 : ℝ) -
                  a * ((q.vertex (Fin.last (e.1 + e.2)) - u).2 : ℝ)) -
                pathWeight ω q < -s}) := by
  have hmain := tilt_change_of_measure_le μ a G0 dl dr Gtop htop hgap
  dsimp only at hmain
  obtain ⟨α, hα, c', hc', hImeas, hmass, hfin⟩ := hmain
  have hφ : 0 < (1 - Gtop) / 4 := by linarith only [hgap]
  have hη : 0 < (100 * (1 + |dl| + |dr|) + 16 * |dr| + 1) / 2 := by positivity
  -- `P(Vᶜ) → 0`: identify `Gtop` with the top-indicator shape.
  have hshape := exists_source_top_indicator_shape_with_strip_rarity μ
  dsimp only at hshape
  obtain ⟨g, -, -, -, -, hlim, -, -, -, -, -, hrare⟩ := hshape
  have hx1 : (((toQuadrant (a, 1 - a)).1 : NNReal) : ℝ) = a := Real.coe_toNNReal a ha0.le
  have hx2 : (((toQuadrant (a, 1 - a)).2 : NNReal) : ℝ) = 1 - a :=
    Real.coe_toNNReal (1 - a) (by linarith only [ha1])
  have hl := hlim (toQuadrant (a, 1 - a))
  rw [hx1, hx2] at hl
  have hgval : g (toQuadrant (a, 1 - a)) = Gtop := tendsto_nhds_unique hl htop
  obtain ⟨-, -, -, hVlim⟩ := hrare a ((1 - Gtop) / 4) ha0 ha1 hφ (by
    rw [hgval]
    linarith only [hgap])
  -- `P(Uᶜ) → 0` from the bad-site rarity.
  have hAmeas := (hImeas.union ((measurableSet_singleton
    (sSup ((fun t : ℝ => (t : EReal)) '' μ.support))).preimage
      continuous_coe_real_ereal.measurable)).compl
  have hUlim := tendsto_closed_strip_bad_sites_probability μ _ hAmeas a _ hφ hmass
  -- `4/λ → 0`.
  have hDlim := tendsto_four_div_cubic_tilt_binomial_mean α ((1 - Gtop) / 4) c'
    ((100 * (1 + |dl| + |dr|) + 16 * |dr| + 1) / 2) hα.1 hφ hc' hη
  dsimp only at hDlim
  have hErr := (hUlim.add hVlim).add hDlim
  rw [add_zero, add_zero] at hErr
  refine ⟨Real.exp (3264 * ((100 * (1 + |dl| + |dr|) + 16 * |dr| + 1) / 2) ^ 2 /
    (α ^ 2 * ((1 - Gtop) / 4) ^ 2 * c' ^ 2)), (Real.exp_pos _).le, _, hErr, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_cubic_tilt_delta_mem_Ioo α
    ((1 - Gtop) / 4) c' ((100 * (1 + |dl| + |dr|) + 16 * |dr| + 1) / 2) hα.1 hφ hc' hη]
    with s hs hδ
  have h := hfin s hs hδ.2
  have hcard := tiltStripRegion_card_bounds a s (Nat.ceil (s ^ 3)) hs
    (cubic_length_ceil_bounds s hs).1
  dsimp only at hcard
  have hcost := cubic_tilt_exponential_cost_bound α ((1 - Gtop) / 4) c'
    ((100 * (1 + |dl| + |dr|) + 16 * |dr| + 1) / 2) s hα.1 hφ hc' hη hs _
    (hcard.1.trans hcard.2)
  exact h.trans (add_mul_le_add_mul (hcost.1.trans hcost.2) (Real.sqrt_nonneg _))

end LPPDifferentiability
end
