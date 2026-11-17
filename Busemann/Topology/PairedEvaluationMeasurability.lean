/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.EvalPlus
public import Busemann.Topology.PairedGraphHitMeasurability
import Busemann.Topology.PairedGraphHitClosedOpen
import Busemann.Topology.SqueezedStateEmbedding
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Separation.Hausdorff

/-! Fixed-time scalar evaluations of the two traces are measurable for the
actual ordered-graph Vietoris Borel space. -/

@[expose] public section
open MeasureTheory
namespace LPP.Busemann

private theorem compressed_abs_lt_one (x : ℝ) : |compressReal x| < 1 := by
  have hd : 0 < 1 + |x| := by positivity
  rw [compressReal, abs_div, abs_of_pos hd]
  exact (div_lt_one hd).2 (by linarith [abs_nonneg x])

private theorem compressed_strictMono : StrictMono compressReal := by
  intro x y hxy
  by_cases hx : 0 ≤ x
  · have hy : 0 ≤ y := le_trans hx hxy.le
    change x / (1 + |x|) < y / (1 + |y|)
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    apply (div_lt_div_iff₀ (by linarith : 0 < 1 + x)
      (by linarith : 0 < 1 + y)).2
    nlinarith
  · by_cases hy : y ≤ 0
    · have hx' : x ≤ 0 := le_trans hxy.le hy
      change x / (1 + |x|) < y / (1 + |y|)
      rw [abs_of_nonpos hx', abs_of_nonpos hy]
      apply (div_lt_div_iff₀ (by linarith : 0 < 1 - x)
        (by linarith : 0 < 1 - y)).2
      nlinarith
    · have hx' : x < 0 := lt_of_not_ge hx
      have hy' : 0 < y := lt_of_not_ge hy
      change x / (1 + |x|) < y / (1 + |y|)
      rw [abs_of_neg hx', abs_of_pos hy']
      exact (div_neg_of_neg_of_pos hx' (by linarith : 0 < 1 - x)).trans
        (div_pos hy' (by linarith : 0 < 1 + y))

private theorem positive_squeeze (t : ℝ) : 0 < squeezeScale t := by
  rw [squeezeScale]
  positivity

private theorem compressed_threshold (t x a : ℝ) :
    squeezeScale t * compressReal x < squeezeScale t * compressReal a ↔ x < a := by
  constructor
  · intro h
    exact compressed_strictMono.lt_iff_lt.mp
      (lt_of_mul_lt_mul_left h (positive_squeeze t).le)
  · intro h
    exact mul_lt_mul_of_pos_left (compressed_strictMono h) (positive_squeeze t)

private theorem finite_trace_of_clock {S : Set ℝ} {J : Type*}
    (f : PairedSkorokhodPath S J) (t : {u : ℝ // u ∈ S})
    (p : SqueezedState J) (hp : p ∈ pairedTraceGraph S f.1)
    (hc : (squeezedStateEmbedding J p).1 = compressReal t.val) :
    p = .finite (f.1.1 t) t.val ∨ p = .finite (f.1.2 t) t.val := by
  rcases hp with hbot | htop | ⟨u, hu⟩
  · rw [hbot] at hc
    simp only [squeezedStateEmbedding] at hc
    have hbound := (abs_lt.mp (compressed_abs_lt_one t.val)).1
    linarith
  · rw [htop] at hc
    simp only [squeezedStateEmbedding] at hc
    have hbound := (abs_lt.mp (compressed_abs_lt_one t.val)).2
    linarith
  · rcases hu with hu | hu
    · rw [hu] at hc ⊢
      simp only [squeezedStateEmbedding] at hc
      have heq : u.val = t.val := compressed_strictMono.injective hc
      have hueq : u = t := Subtype.ext heq
      subst u
      exact Or.inl rfl
    · rw [hu] at hc ⊢
      simp only [squeezedStateEmbedding] at hc
      have heq : u.val = t.val := compressed_strictMono.injective hc
      have hueq : u = t := Subtype.ext heq
      subst u
      exact Or.inr rfl

private theorem directed_pair_of_offdiagonal {S : Set ℝ} {J : Type*}
    (f : PairedSkorokhodPath S J) (t : {u : ℝ // u ∈ S})
    (z : SqueezedState J × SqueezedState J)
    (hz : z ∈ pairedPathOrderGraph S J f)
    (hclock₁ : (squeezedStateEmbedding J z.1).1 = compressReal t.val)
    (hclock₂ : (squeezedStateEmbedding J z.2).1 = compressReal t.val)
    (hne : z.1 ≠ z.2) :
    z.1 = .finite (f.1.1 t) t.val ∧
      z.2 = .finite (f.1.2 t) t.val := by
  have hord : pairedTraceLE S f.1 z.1 z.2 := hz.2.2
  rcases hord with heq | hbot | htop | hstrict | hequal
  · exact False.elim (hne heq)
  · rw [hbot] at hclock₁
    simp only [squeezedStateEmbedding] at hclock₁
    have hbound := (abs_lt.mp (compressed_abs_lt_one t.val)).1
    linarith
  · rw [htop] at hclock₂
    simp only [squeezedStateEmbedding] at hclock₂
    have hbound := (abs_lt.mp (compressed_abs_lt_one t.val)).2
    linarith
  · rcases hstrict with ⟨x, y, u, v, hu, hv, huv⟩
    rw [hu] at hclock₁
    rw [hv] at hclock₂
    simp only [squeezedStateEmbedding] at hclock₁ hclock₂
    have hut : u = t.val := compressed_strictMono.injective hclock₁
    have hvt : v = t.val := compressed_strictMono.injective hclock₂
    exact False.elim (lt_irrefl _ (hut ▸ hvt ▸ huv))
  · rcases hequal with ⟨u, hu, hv⟩
    rw [hu] at hclock₁
    simp only [squeezedStateEmbedding] at hclock₁
    have hut : u.val = t.val := compressed_strictMono.injective hclock₁
    have hueq : u = t := Subtype.ext hut
    subst u
    exact ⟨hu, hv⟩

private theorem canonical_pair_in_graph {S : Set ℝ} {J : Type*}
    (f : PairedSkorokhodPath S J) (t : {u : ℝ // u ∈ S}) :
    (SqueezedState.finite (f.1.1 t) t.val,
      SqueezedState.finite (f.1.2 t) t.val) ∈ pairedPathOrderGraph S J f := by
  change (SqueezedState.finite (f.1.1 t) t.val,
    SqueezedState.finite (f.1.2 t) t.val) ∈ pairedOrderGraph S f.1
  refine ⟨?_, ?_, ?_⟩
  · exact Or.inr (Or.inr ⟨t, Or.inl rfl⟩)
  · exact Or.inr (Or.inr ⟨t, Or.inr rfl⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, rfl, rfl⟩)))

private theorem offdiagonal_hit_iff {S : Set ℝ} {J : Type*}
    (f : PairedSkorokhodPath S J) (t : {u : ℝ // u ∈ S}) :
    (pairedPathOrderGraph S J f ∩
      ({z | (squeezedStateEmbedding J z.1).1 = compressReal t.val ∧
        (squeezedStateEmbedding J z.2).1 = compressReal t.val} ∩
        {z | z.1 ≠ z.2})).Nonempty ↔ f.1.1 t ≠ f.1.2 t := by
  constructor
  · rintro ⟨z, hz, ⟨⟨hc₁, hc₂⟩, hne⟩⟩
    obtain ⟨hm, hp⟩ := directed_pair_of_offdiagonal f t z hz hc₁ hc₂ hne
    intro heq
    apply hne
    simp only [hm, hp, heq]
  · intro hne
    refine ⟨(SqueezedState.finite (f.1.1 t) t.val,
      SqueezedState.finite (f.1.2 t) t.val), canonical_pair_in_graph f t,
      ?_⟩
    constructor
    · constructor <;> rfl
    · intro hpair
      exact hne (SqueezedState.finite.inj hpair).1

private theorem offdiagonal_threshold_iff {S : Set ℝ} {J : Type*}
    (f : PairedSkorokhodPath S J) (t : {u : ℝ // u ∈ S})
    (j : J) (a : ℝ) (minus : Bool) :
    (pairedPathOrderGraph S J f ∩
      ({z | (squeezedStateEmbedding J z.1).1 = compressReal t.val ∧
        (squeezedStateEmbedding J z.2).1 = compressReal t.val} ∩
        {z | z.1 ≠ z.2 ∧
          (squeezedStateEmbedding J (if minus then z.1 else z.2)).2 j <
            squeezeScale t.val * compressReal a})).Nonempty ↔
      f.1.1 t ≠ f.1.2 t ∧
        (if minus then f.1.1 t j else f.1.2 t j) < a := by
  constructor
  · rintro ⟨z, hz, ⟨⟨hc₁, hc₂⟩, hne, hlt⟩⟩
    obtain ⟨hm, hp⟩ := directed_pair_of_offdiagonal f t z hz hc₁ hc₂ hne
    have hdistinct : f.1.1 t ≠ f.1.2 t := by
      intro heq
      apply hne
      simp only [hm, hp, heq]
    refine ⟨hdistinct, ?_⟩
    cases minus <;> simp only [Bool.false_eq_true, ↓reduceIte, hp, hm,
      squeezedStateEmbedding] at hlt ⊢
    · exact (compressed_threshold t.val (f.1.2 t j) a).mp hlt
    · exact (compressed_threshold t.val (f.1.1 t j) a).mp hlt
  · rintro ⟨hne, hlt⟩
    refine ⟨(SqueezedState.finite (f.1.1 t) t.val,
      SqueezedState.finite (f.1.2 t) t.val), canonical_pair_in_graph f t,
      ?_⟩
    constructor
    · constructor <;> rfl
    · constructor
      · intro hpair
        exact hne (SqueezedState.finite.inj hpair).1
      · cases minus <;> simp only [Bool.false_eq_true, ↓reduceIte,
          squeezedStateEmbedding] at hlt ⊢
        · exact (compressed_threshold t.val (f.1.2 t j) a).mpr hlt
        · exact (compressed_threshold t.val (f.1.1 t j) a).mpr hlt

private theorem diagonal_threshold_of_no_jump {S : Set ℝ} {J : Type*}
    (f : PairedSkorokhodPath S J) (t : {u : ℝ // u ∈ S})
    (j : J) (a : ℝ) (hcollapsed : f.1.1 t = f.1.2 t) :
    (pairedPathOrderGraph S J f ∩
      (({z | (squeezedStateEmbedding J z.1).1 = compressReal t.val ∧
        (squeezedStateEmbedding J z.2).1 = compressReal t.val} ∩
        {z | z.1 = z.2}) ∩
        {z | (squeezedStateEmbedding J z.1).2 j <
          squeezeScale t.val * compressReal a})).Nonempty ↔
      f.1.1 t j < a := by
  constructor
  · rintro ⟨z, hz, ⟨⟨⟨hc₁, _⟩, _⟩, hlt⟩⟩
    have hclass := finite_trace_of_clock f t z.1 hz.1 hc₁
    rcases hclass with hm | hp
    · change (squeezedStateEmbedding J z.1).2 j <
        squeezeScale t.val * compressReal a at hlt
      rw [hm] at hlt
      exact (compressed_threshold t.val (f.1.1 t j) a).mp hlt
    · change (squeezedStateEmbedding J z.1).2 j <
        squeezeScale t.val * compressReal a at hlt
      rw [hp, ← hcollapsed] at hlt
      exact (compressed_threshold t.val (f.1.1 t j) a).mp hlt
  · intro hlt
    refine ⟨(SqueezedState.finite (f.1.1 t) t.val,
      SqueezedState.finite (f.1.2 t) t.val), canonical_pair_in_graph f t,
      ?_⟩
    constructor
    · constructor
      · constructor <;> rfl
      · change SqueezedState.finite (f.1.1 t) t.val =
          SqueezedState.finite (f.1.2 t) t.val
        rw [hcollapsed]
    · exact (compressed_threshold t.val (f.1.1 t j) a).mpr hlt

-- The named parameter `hS` is part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- At a fixed actual time and coordinate, both traces are measurable for the
ordered-graph Vietoris Borel structure. -/
theorem measurable_evalMinus_evalPlus
    (S : Set ℝ) (J : Type*) [Countable J] (hS : IsClosed S)
    (t : {u : ℝ // u ∈ S}) (j : J) :
    Measurable (fun f : PairedSkorokhodPath S J => evalMinus f t j) ∧
    Measurable (fun f : PairedSkorokhodPath S J => evalPlus f t j) := by
  let e : SqueezedState J → ℝ × (J → ℝ) := squeezedStateEmbedding J
  let C : Set (SqueezedState J × SqueezedState J) :=
    {z | (e z.1).1 = compressReal t.val ∧
      (e z.2).1 = compressReal t.val}
  let D : Set (SqueezedState J × SqueezedState J) := {z | z.1 = z.2}
  let O : Set (SqueezedState J × SqueezedState J) := {z | z.1 ≠ z.2}
  let Om : ℝ → Set (SqueezedState J × SqueezedState J) := fun a =>
    {z | z.1 ≠ z.2 ∧ (e z.1).2 j < squeezeScale t.val * compressReal a}
  let Op : ℝ → Set (SqueezedState J × SqueezedState J) := fun a =>
    {z | z.1 ≠ z.2 ∧ (e z.2).2 j < squeezeScale t.val * compressReal a}
  let Od : ℝ → Set (SqueezedState J × SqueezedState J) := fun a =>
    {z | (e z.1).2 j < squeezeScale t.val * compressReal a}
  have he : Continuous e := by
    change Continuous (squeezedStateEmbedding J)
    exact continuous_induced_dom
  have hclock₁ : Continuous (fun z : SqueezedState J × SqueezedState J => (e z.1).1) :=
    continuous_fst.comp (he.comp continuous_fst)
  have hclock₂ : Continuous (fun z : SqueezedState J × SqueezedState J => (e z.2).1) :=
    continuous_fst.comp (he.comp continuous_snd)
  have hC : IsClosed C := by
    exact (isClosed_eq hclock₁ continuous_const).inter
      (isClosed_eq hclock₂ continuous_const)
  let : T2Space (SqueezedState J) :=
    (Topology.IsEmbedding.induced (squeezedStateEmbedding_injective J)).t2Space
  have hD : IsClosed D := isClosed_diagonal
  have hO : IsOpen O := hD.isOpen_compl
  have hscalar₁ : Continuous (fun z : SqueezedState J × SqueezedState J => (e z.1).2 j) :=
    ((continuous_apply j).comp continuous_snd).comp (he.comp continuous_fst)
  have hscalar₂ : Continuous (fun z : SqueezedState J × SqueezedState J => (e z.2).2 j) :=
    ((continuous_apply j).comp continuous_snd).comp (he.comp continuous_snd)
  have hOm (a : ℝ) : IsOpen (Om a) :=
    hO.inter (isOpen_Iio.preimage hscalar₁)
  have hOp (a : ℝ) : IsOpen (Op a) :=
    hO.inter (isOpen_Iio.preimage hscalar₂)
  have hOd (a : ℝ) : IsOpen (Od a) := isOpen_Iio.preimage hscalar₁
  have hJump : MeasurableSet {f : PairedSkorokhodPath S J |
      (pairedPathOrderGraph S J f ∩ (C ∩ O)).Nonempty} :=
    measurableSet_pairedPathOrderGraph_hit_closed_inter_open S J C O hC hO
  have hMinus (a : ℝ) : MeasurableSet {f : PairedSkorokhodPath S J |
      (pairedPathOrderGraph S J f ∩ (C ∩ Om a)).Nonempty} :=
    measurableSet_pairedPathOrderGraph_hit_closed_inter_open S J C (Om a) hC (hOm a)
  have hPlus (a : ℝ) : MeasurableSet {f : PairedSkorokhodPath S J |
      (pairedPathOrderGraph S J f ∩ (C ∩ Op a)).Nonempty} :=
    measurableSet_pairedPathOrderGraph_hit_closed_inter_open S J C (Op a) hC (hOp a)
  have hDiag (a : ℝ) : MeasurableSet {f : PairedSkorokhodPath S J |
      (pairedPathOrderGraph S J f ∩ ((C ∩ D) ∩ Od a)).Nonempty} :=
    measurableSet_pairedPathOrderGraph_hit_closed_inter_open S J (C ∩ D) (Od a)
      (hC.inter hD) (hOd a)
  constructor
  · apply measurable_of_Iio
    intro a
    have hevent : {f : PairedSkorokhodPath S J | evalMinus f t j < a} =
        {f | (pairedPathOrderGraph S J f ∩ (C ∩ Om a)).Nonempty} ∪
          ({f | (pairedPathOrderGraph S J f ∩ (C ∩ O)).Nonempty}ᶜ ∩
            {f | (pairedPathOrderGraph S J f ∩ ((C ∩ D) ∩ Od a)).Nonempty}) := by
      ext f
      have hjump : (pairedPathOrderGraph S J f ∩ (C ∩ O)).Nonempty ↔
          f.1.1 t ≠ f.1.2 t := offdiagonal_hit_iff f t
      have hm : (pairedPathOrderGraph S J f ∩ (C ∩ Om a)).Nonempty ↔
          f.1.1 t ≠ f.1.2 t ∧ f.1.1 t j < a := by
        simpa [Om, C, e] using offdiagonal_threshold_iff f t j a true
      by_cases hne : f.1.1 t ≠ f.1.2 t
      · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
          Set.mem_compl_iff]
        rw [hjump, hm]
        simp [evalMinus, hne]
      · have heq : f.1.1 t = f.1.2 t := not_ne_iff.mp hne
        have hd : (pairedPathOrderGraph S J f ∩ ((C ∩ D) ∩ Od a)).Nonempty ↔
            f.1.1 t j < a := by
          simpa [C, D, Od, e] using diagonal_threshold_of_no_jump f t j a heq
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
          Set.mem_compl_iff]
        rw [hjump, hm, hd]
        simp [evalMinus, hne]
    rw [show (fun f : PairedSkorokhodPath S J => evalMinus f t j) ⁻¹' Set.Iio a =
      {f | evalMinus f t j < a} from rfl, hevent]
    exact (hMinus a).union (hJump.compl.inter (hDiag a))
  · apply measurable_of_Iio
    intro a
    have hevent : {f : PairedSkorokhodPath S J | evalPlus f t j < a} =
        {f | (pairedPathOrderGraph S J f ∩ (C ∩ Op a)).Nonempty} ∪
          ({f | (pairedPathOrderGraph S J f ∩ (C ∩ O)).Nonempty}ᶜ ∩
            {f | (pairedPathOrderGraph S J f ∩ ((C ∩ D) ∩ Od a)).Nonempty}) := by
      ext f
      have hjump : (pairedPathOrderGraph S J f ∩ (C ∩ O)).Nonempty ↔
          f.1.1 t ≠ f.1.2 t := offdiagonal_hit_iff f t
      have hp : (pairedPathOrderGraph S J f ∩ (C ∩ Op a)).Nonempty ↔
          f.1.1 t ≠ f.1.2 t ∧ f.1.2 t j < a := by
        simpa [Op, C, e] using offdiagonal_threshold_iff f t j a false
      by_cases hne : f.1.1 t ≠ f.1.2 t
      · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
          Set.mem_compl_iff]
        rw [hjump, hp]
        simp [evalPlus, hne]
      · have heq : f.1.1 t = f.1.2 t := not_ne_iff.mp hne
        have hd : (pairedPathOrderGraph S J f ∩ ((C ∩ D) ∩ Od a)).Nonempty ↔
            f.1.1 t j < a := by
          simpa [C, D, Od, e] using diagonal_threshold_of_no_jump f t j a heq
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
          Set.mem_compl_iff]
        rw [hjump, hp, hd]
        simp [evalPlus, heq]
    rw [show (fun f : PairedSkorokhodPath S J => evalPlus f t j) ⁻¹' Set.Iio a =
      {f | evalPlus f t j < a} from rfl, hevent]
    exact (hPlus a).union (hJump.compl.inter (hDiag a))

end LPP.Busemann
