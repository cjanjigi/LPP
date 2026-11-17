/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.SupportTilt
public import Busemann.Process.Shifts
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-! The four literal one-sided unit envelopes of an ordered countable raw array. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

private theorem envelope_bounds {α : Type*} [CompleteLinearOrder α]
    (t : ℕ → ℝ) (f : ℕ → α)
    (horder : ∀ j k, t j ≤ t k → f k ≤ f j)
    (u : ℝ) (l r : ℕ) (hl : t l < u) (hr : u < t r) :
    let L := ⨅ j, if t j < u then f j else ⊤
    let U := ⨆ j, if u < t j then f j else ⊥
    (f r ≤ L ∧ L ≤ f l) ∧ (f r ≤ U ∧ U ≤ f l) := by
  classical
  dsimp only
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine le_iInf fun j => ?_
    split_ifs with hj
    · exact horder j r (hj.trans hr).le
    · exact le_top
  · exact iInf_le_of_le l (by rw [ite_eq_left hl])
  · exact le_iSup_of_le r (by rw [ite_eq_left hr])
  · refine iSup_le fun j => ?_
    split_ifs with hj
    · exact horder l j (hl.trans hj).le
    · exact bot_le

private theorem upper_envelope_le_lower {α : Type*} [CompleteLinearOrder α]
    (t : ℕ → ℝ) (f : ℕ → α)
    (horder : ∀ j k, t j ≤ t k → f k ≤ f j) (u : ℝ) :
    (⨆ j, if u < t j then f j else ⊥) ≤
      ⨅ j, if t j < u then f j else ⊤ := by
  classical
  refine iSup_le fun j => ?_
  split_ifs with hj
  · refine le_iInf fun k => ?_
    split_ifs with hk
    · exact horder k j (hk.trans hj).le
    · exact le_top
  · exact bot_le

private theorem lower_envelope_cofinal {α : Type*} [CompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α]
    (t : ℕ → ℝ) (f : ℕ → α)
    (horder : ∀ j k, t j ≤ t k → f k ≤ f j)
    (u : ℝ) (a : ℕ → ℕ) (hmono : StrictMono (fun n => t (a n)))
    (hside : ∀ n, t (a n) < u)
    (hlimit : Tendsto (fun n => t (a n)) atTop (𝓝 u)) :
    Tendsto (fun n => f (a n)) atTop
      (𝓝 (⨅ j, if t j < u then f j else ⊤)) := by
  classical
  have hanti : Antitone (fun n => f (a n)) := fun n m hnm =>
    horder (a n) (a m) (hmono.monotone hnm)
  have heq : (⨅ n, f (a n)) = ⨅ j, if t j < u then f j else ⊤ := by
    apply le_antisymm
    · refine le_iInf fun j => ?_
      split_ifs with hj
      · obtain ⟨n, hn⟩ := (Filter.Tendsto.eventually_const_lt hj hlimit).exists
        exact (iInf_le _ n).trans (horder j (a n) hn.le)
      · exact le_top
    · exact le_iInf fun n => iInf_le_of_le (a n) (by rw [ite_eq_left (hside n)])
  simpa only [heq] using tendsto_atTop_iInf hanti

private theorem upper_envelope_cofinal {α : Type*} [CompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α]
    (t : ℕ → ℝ) (f : ℕ → α)
    (horder : ∀ j k, t j ≤ t k → f k ≤ f j)
    (u : ℝ) (b : ℕ → ℕ) (hmono : StrictAnti (fun n => t (b n)))
    (hside : ∀ n, u < t (b n))
    (hlimit : Tendsto (fun n => t (b n)) atTop (𝓝 u)) :
    Tendsto (fun n => f (b n)) atTop
      (𝓝 (⨆ j, if u < t j then f j else ⊥)) := by
  classical
  have hmono' : Monotone (fun n => f (b n)) := fun n m hnm =>
    horder (b m) (b n) (hmono.antitone hnm)
  have heq : (⨆ n, f (b n)) = ⨆ j, if u < t j then f j else ⊥ := by
    apply le_antisymm
    · exact iSup_le fun n => le_iSup_of_le (b n) (by rw [ite_eq_left (hside n)])
    · refine iSup_le fun j => ?_
      split_ifs with hj
      · obtain ⟨n, hn⟩ := (Filter.Tendsto.eventually_lt_const hj hlimit).exists
        exact (horder (b n) j hn.le).trans (le_iSup (fun n => f (b n)) n)
      · exact bot_le
  simpa only [heq] using tendsto_atTop_iSup hmono'

private theorem finite_of_real_bounds (a : EReal) (l u : ℝ)
    (hl : (l : EReal) ≤ a) (hu : a ≤ (u : EReal)) : a ≠ ⊤ ∧ a ≠ ⊥ :=
  ⟨(hu.trans_lt (EReal.coe_lt_top u)).ne,
    ((EReal.bot_lt_coe l).trans_le hl).ne'⟩

private theorem measurable_raw_site (j : ℕ) :
    Measurable (fun q : Lattice × Fin 2 × ProcessSample => q.2.2.2 j q.1 q.2.1) := by
  apply measurable_from_prod_countable_right
  intro x
  apply measurable_from_prod_countable_right
  intro i
  exact (measurable_pi_apply i).comp
    ((measurable_pi_apply x).comp ((measurable_pi_apply j).comp measurable_snd))

/-- The literal left/right unit envelopes are measurable, finite on one raw
order event, and are the limits along every cofinal dense-index sequence.
This is the deterministic one-sided construction after (4.18) in JR1810.03580v3. -/
theorem countable_unit_envelopes_measurable_finite_and_cofinal
    (g : Quadrant → ℝ) (D : ℕ → SupportTilt g)
    (happrox : ∀ h : SupportTilt g, ∃ a b : ℕ → ℕ,
      StrictMono (fun n => (D (a n)).1.1) ∧
      StrictAnti (fun n => (D (b n)).1.1) ∧
      (∀ n, (D (a n)).1.1 < h.1.1 ∧ h.1.1 < (D (b n)).1.1) ∧
      Tendsto (fun n => (D (a n)).1) atTop (𝓝 h.1) ∧
      Tendsto (fun n => (D (b n)).1) atTop (𝓝 h.1)) :
    let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ := fun j x i s => s.2 j x i
    let Q : Set ProcessSample := {s | ∀ j k x,
      (D j).1.1 ≤ (D k).1.1 → X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
    let Eminus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
      fun h x i s => if i = 0 then
        ⨅ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊤
      else ⨆ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊥
    let Eplus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
      fun h x i s => if i = 0 then
        ⨆ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊥
      else ⨅ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊤
    let eMinus := fun h x i s => (Eminus h x i s).toReal
    let ePlus := fun h x i s => (Eplus h x i s).toReal
    MeasurableSet Q ∧
    (∀ z s, processShift z s ∈ Q ↔ s ∈ Q) ∧
    Measurable (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample =>
      Eminus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    Measurable (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample =>
      Eplus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    Measurable (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample =>
      eMinus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    Measurable (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample =>
      ePlus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    (∀ s ∈ Q, ∀ h x i,
      Eminus h x i s ≠ ⊤ ∧ Eminus h x i s ≠ ⊥ ∧
      Eplus h x i s ≠ ⊤ ∧ Eplus h x i s ≠ ⊥) ∧
    (∀ s ∈ Q, ∀ h x,
      ePlus h x 0 s ≤ eMinus h x 0 s ∧ eMinus h x 1 s ≤ ePlus h x 1 s) ∧
    (∀ s ∈ Q, ∀ h k : SupportTilt g, h.1.1 < k.1.1 → ∀ x,
      eMinus k x 0 s ≤ ePlus h x 0 s ∧ ePlus h x 1 s ≤ eMinus k x 1 s) ∧
    (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ a : ℕ → ℕ,
      StrictMono (fun n => (D (a n)).1.1) →
      (∀ n, (D (a n)).1.1 < h.1.1) →
      Tendsto (fun n => (D (a n)).1) atTop (𝓝 h.1) →
      ∀ x i, Tendsto (fun n => X (a n) x i s) atTop (𝓝 (eMinus h x i s))) ∧
    (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ b : ℕ → ℕ,
      StrictAnti (fun n => (D (b n)).1.1) →
      (∀ n, h.1.1 < (D (b n)).1.1) →
      Tendsto (fun n => (D (b n)).1) atTop (𝓝 h.1) →
      ∀ x i, Tendsto (fun n => X (b n) x i s) atTop (𝓝 (ePlus h x i s))) := by
  classical
  let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ := fun j x i s => s.2 j x i
  let Q : Set ProcessSample := {s | ∀ j k x,
      (D j).1.1 ≤ (D k).1.1 → X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
  let Eminus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
      fun h x i s => if i = 0 then
        ⨅ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊤
      else ⨆ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊥
  let Eplus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
      fun h x i s => if i = 0 then
        ⨆ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊥
      else ⨅ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊤
  let eMinus := fun h x i s => (Eminus h x i s).toReal
  let ePlus := fun h x i s => (Eplus h x i s).toReal
  change MeasurableSet Q ∧
    (∀ z s, processShift z s ∈ Q ↔ s ∈ Q) ∧
    Measurable (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample =>
      Eminus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    Measurable (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample =>
      Eplus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    Measurable (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample =>
      eMinus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    Measurable (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample =>
      ePlus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    (∀ s ∈ Q, ∀ h x i,
      Eminus h x i s ≠ ⊤ ∧ Eminus h x i s ≠ ⊥ ∧
      Eplus h x i s ≠ ⊤ ∧ Eplus h x i s ≠ ⊥) ∧
    (∀ s ∈ Q, ∀ h x,
      ePlus h x 0 s ≤ eMinus h x 0 s ∧ eMinus h x 1 s ≤ ePlus h x 1 s) ∧
    (∀ s ∈ Q, ∀ h k : SupportTilt g, h.1.1 < k.1.1 → ∀ x,
      eMinus k x 0 s ≤ ePlus h x 0 s ∧ ePlus h x 1 s ≤ eMinus k x 1 s) ∧
    (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ a : ℕ → ℕ,
      StrictMono (fun n => (D (a n)).1.1) →
      (∀ n, (D (a n)).1.1 < h.1.1) →
      Tendsto (fun n => (D (a n)).1) atTop (𝓝 h.1) →
      ∀ x i, Tendsto (fun n => X (a n) x i s) atTop (𝓝 (eMinus h x i s))) ∧
    (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ b : ℕ → ℕ,
      StrictAnti (fun n => (D (b n)).1.1) →
      (∀ n, h.1.1 < (D (b n)).1.1) →
      Tendsto (fun n => (D (b n)).1) atTop (𝓝 h.1) →
      ∀ x i, Tendsto (fun n => X (b n) x i s) atTop (𝓝 (ePlus h x i s)))
  let t : ℕ → ℝ := fun j => (D j).1.1
  have hraw (j : ℕ) (x : Lattice) (i : Fin 2) : Measurable (X j x i) :=
    (measurable_pi_apply i).comp
      ((measurable_pi_apply x).comp ((measurable_pi_apply j).comp measurable_snd))
  -- The raw event is countable, and shifts only reindex its sites.
  have hQ : MeasurableSet Q := by
    change MeasurableSet {s | ∀ j k x, (D j).1.1 ≤ (D k).1.1 →
      X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro x
    apply MeasurableSet.iInter
    intro _hjk
    exact (measurableSet_le (hraw k x 0) (hraw j x 0)).inter
      (measurableSet_le (hraw j x 1) (hraw k x 1))
  have hforward (z : Lattice) (s : ProcessSample) (hs : s ∈ Q) :
      processShift z s ∈ Q := by
    intro j k x hjk
    exact hs j k (z + x) hjk
  have hshift (z : Lattice) (s : ProcessSample) : processShift z s ∈ Q ↔ s ∈ Q := by
    constructor
    · intro hs
      have hb := hforward (-z) (processShift z s) hs
      rwa [processShift_neg_processShift] at hb
    · exact hforward z s
  -- All four extrema have a fixed countable index, with measurable moving guards.
  have hrawJoint (j : ℕ) : Measurable
      (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample =>
        (X j q.2.1 q.2.2.1 q.2.2.2 : EReal)) :=
    ((measurable_raw_site j).comp measurable_snd).coe_real_ereal
  have hh : Measurable
      (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample => q.1.1.1) := by
    fun_prop
  have hi : MeasurableSet
      {q : SupportTilt g × Lattice × Fin 2 × ProcessSample | q.2.2.1 = 0} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hEm : Measurable (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample =>
      Eminus q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    apply Measurable.ite hi
    · exact Measurable.iInf fun j => Measurable.ite
        (measurableSet_lt measurable_const hh) (hrawJoint j) measurable_const
    · exact Measurable.iSup fun j => Measurable.ite
        (measurableSet_lt measurable_const hh) (hrawJoint j) measurable_const
  have hEp : Measurable (fun q : SupportTilt g × Lattice × Fin 2 × ProcessSample =>
      Eplus q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    apply Measurable.ite hi
    · exact Measurable.iSup fun j => Measurable.ite
        (measurableSet_lt hh measurable_const) (hrawJoint j) measurable_const
    · exact Measurable.iInf fun j => Measurable.ite
        (measurableSet_lt hh measurable_const) (hrawJoint j) measurable_const
  have horder0 (s : ProcessSample) (hs : s ∈ Q) (x : Lattice) :
      ∀ j k, t j ≤ t k → (X k x 0 s : EReal) ≤ (X j x 0 s : EReal) := by
    intro j k hjk
    exact EReal.coe_le_coe (hs j k x hjk).1
  have horder1 (s : ProcessSample) (hs : s ∈ Q) (x : Lattice) :
      ∀ j k, t j ≤ t k → OrderDual.toDual (X k x 1 s : EReal) ≤
        OrderDual.toDual (X j x 1 s : EReal) := by
    intro j k hjk
    exact EReal.coe_le_coe (hs j k x hjk).2
  -- One lower and one upper raw value bracket both signs at once.
  have hfinite (s : ProcessSample) (hs : s ∈ Q) (h : SupportTilt g) (x : Lattice)
      (i : Fin 2) : Eminus h x i s ≠ ⊤ ∧ Eminus h x i s ≠ ⊥ ∧
        Eplus h x i s ≠ ⊤ ∧ Eplus h x i s ≠ ⊥ := by
    obtain ⟨a, b, _, _, hab, _, _⟩ := happrox h
    have he := envelope_bounds t (fun j => (X j x 0 s : EReal))
      (horder0 s hs x) h.1.1 (a 0) (b 0) (hab 0).1 (hab 0).2
    have hn := envelope_bounds t (fun j => (OrderDual.toDual (X j x 1 s : EReal)))
      (horder1 s hs x) h.1.1 (a 0) (b 0) (hab 0).1 (hab 0).2
    fin_cases i
    · have hme := finite_of_real_bounds (Eminus h x 0 s)
        (X (b 0) x 0 s) (X (a 0) x 0 s) he.1.1 he.1.2
      have hpe := finite_of_real_bounds (Eplus h x 0 s)
        (X (b 0) x 0 s) (X (a 0) x 0 s) he.2.1 he.2.2
      exact ⟨hme.1, hme.2, hpe.1, hpe.2⟩
    · have hmn := finite_of_real_bounds (Eminus h x 1 s)
        (X (a 0) x 1 s) (X (b 0) x 1 s) hn.1.2 hn.1.1
      have hpn := finite_of_real_bounds (Eplus h x 1 s)
        (X (a 0) x 1 s) (X (b 0) x 1 s) hn.2.2 hn.2.1
      exact ⟨hmn.1, hmn.2, hpn.1, hpn.2⟩
  have hwithin (s : ProcessSample) (hs : s ∈ Q) (h : SupportTilt g) (x : Lattice) :
      ePlus h x 0 s ≤ eMinus h x 0 s ∧ eMinus h x 1 s ≤ ePlus h x 1 s := by
    have he : Eplus h x 0 s ≤ Eminus h x 0 s :=
      upper_envelope_le_lower t _ (horder0 s hs x) h.1.1
    have hn : Eminus h x 1 s ≤ Eplus h x 1 s :=
      upper_envelope_le_lower t _ (horder1 s hs x) h.1.1
    exact ⟨EReal.toReal_le_toReal he (hfinite s hs h x 0).2.2.2
        (hfinite s hs h x 0).1,
      EReal.toReal_le_toReal hn (hfinite s hs h x 1).2.1
        (hfinite s hs h x 1).2.2.1⟩
  have hcross (s : ProcessSample) (hs : s ∈ Q) (h k : SupportTilt g)
      (hhk : h.1.1 < k.1.1) (x : Lattice) :
      eMinus k x 0 s ≤ ePlus h x 0 s ∧ ePlus h x 1 s ≤ eMinus k x 1 s := by
    obtain ⟨a, b, _, _, hab, _, hb⟩ := happrox h
    have ht : Tendsto (fun n => t (b n)) atTop (𝓝 h.1.1) :=
      (continuous_fst.tendsto h.1).comp hb
    obtain ⟨n, hn⟩ := (Filter.Tendsto.eventually_lt_const hhk ht).exists
    have heL : Eminus k x 0 s ≤ (X (b n) x 0 s : EReal) := by
      change (⨅ j, if t j < k.1.1 then (X j x 0 s : EReal) else ⊤) ≤ _
      exact iInf_le_of_le (b n) (by rw [ite_eq_left hn])
    have heR : (X (b n) x 0 s : EReal) ≤ Eplus h x 0 s := by
      change _ ≤ ⨆ j, if h.1.1 < t j then (X j x 0 s : EReal) else ⊥
      exact le_iSup_of_le (b n) (by rw [ite_eq_left (hab n).2])
    have hvL : Eplus h x 1 s ≤ (X (b n) x 1 s : EReal) := by
      change (⨅ j, if h.1.1 < t j then (X j x 1 s : EReal) else ⊤) ≤ _
      exact iInf_le_of_le (b n) (by rw [ite_eq_left (hab n).2])
    have hvR : (X (b n) x 1 s : EReal) ≤ Eminus k x 1 s := by
      change _ ≤ ⨆ j, if t j < k.1.1 then (X j x 1 s : EReal) else ⊥
      exact le_iSup_of_le (b n) (by rw [ite_eq_left hn])
    have he : Eminus k x 0 s ≤ Eplus h x 0 s := heL.trans heR
    have hv : Eplus h x 1 s ≤ Eminus k x 1 s := hvL.trans hvR
    exact ⟨EReal.toReal_le_toReal he (hfinite s hs k x 0).2.1
        (hfinite s hs h x 0).2.2.1,
      EReal.toReal_le_toReal hv (hfinite s hs h x 1).2.2.2
        (hfinite s hs k x 1).1⟩
  have hlower (s : ProcessSample) (hs : s ∈ Q) (h : SupportTilt g) (a : ℕ → ℕ)
      (hm : StrictMono (fun n => (D (a n)).1.1))
      (ha : ∀ n, (D (a n)).1.1 < h.1.1)
      (ht : Tendsto (fun n => (D (a n)).1) atTop (𝓝 h.1)) (x : Lattice) (i : Fin 2) :
      Tendsto (fun n => X (a n) x i s) atTop (𝓝 (eMinus h x i s)) := by
    have ht' : Tendsto (fun n => t (a n)) atTop (𝓝 h.1.1) :=
      (continuous_fst.tendsto h.1).comp ht
    have hE : Tendsto (fun n => (X (a n) x i s : EReal)) atTop
        (𝓝 (Eminus h x i s)) := by
      fin_cases i
      · exact lower_envelope_cofinal t _ (horder0 s hs x) h.1.1 a hm ha ht'
      · exact lower_envelope_cofinal t _ (horder1 s hs x) h.1.1 a hm ha ht'
    have hf := hfinite s hs h x i
    simpa only [Function.comp_def, EReal.toReal_coe] using (EReal.tendsto_toReal hf.1 hf.2.1).comp hE
  have hupper (s : ProcessSample) (hs : s ∈ Q) (h : SupportTilt g) (b : ℕ → ℕ)
      (hm : StrictAnti (fun n => (D (b n)).1.1))
      (hb : ∀ n, h.1.1 < (D (b n)).1.1)
      (ht : Tendsto (fun n => (D (b n)).1) atTop (𝓝 h.1)) (x : Lattice) (i : Fin 2) :
      Tendsto (fun n => X (b n) x i s) atTop (𝓝 (ePlus h x i s)) := by
    have ht' : Tendsto (fun n => t (b n)) atTop (𝓝 h.1.1) :=
      (continuous_fst.tendsto h.1).comp ht
    have hE : Tendsto (fun n => (X (b n) x i s : EReal)) atTop
        (𝓝 (Eplus h x i s)) := by
      fin_cases i
      · exact upper_envelope_cofinal t _ (horder0 s hs x) h.1.1 b hm hb ht'
      · exact upper_envelope_cofinal t _ (horder1 s hs x) h.1.1 b hm hb ht'
    have hf := hfinite s hs h x i
    simpa only [Function.comp_def, EReal.toReal_coe] using (EReal.tendsto_toReal hf.2.2.1 hf.2.2.2).comp hE
  exact ⟨hQ, hshift, hEm, hEp, hEm.ereal_toReal, hEp.ereal_toReal,
    hfinite, hwithin, hcross, hlower, hupper⟩

end LPP.Busemann
