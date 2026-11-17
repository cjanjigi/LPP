/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.PairedOrderGraph
public import Busemann.Topology.SqueezedStateLimits
import Mathlib.Topology.Sequences
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Finite ordered pairs of paired traces

The literal paired order places the first time no later than the second.
This module develops the common-subsequence limit for finite trace pairs.
-/

@[expose] public section
open Filter
open scoped Topology
namespace LPP.Busemann

private theorem finite_order_time_le {S : Set ℝ} {J : Type*}
    (f : RawPairedTrace S J) {v w : J → ℝ} {t u : ℝ}
    (h : pairedTraceLE S f (.finite v t) (.finite w u)) : t ≤ u := by
  rcases h with h | h | h | h | h
  · have htime : t = u := by
      cases h
      rfl
    exact htime.le
  · cases h
  · cases h
  · rcases h with ⟨_, _, t', u', hp, hq, hlt⟩
    cases hp
    cases hq
    exact hlt.le
  · rcases h with ⟨s, hp, hq⟩
    cases hp
    cases hq
    exact le_refl _

private theorem ordered_finite_times_le {S : Set ℝ} {J : Type*}
    (f : RawPairedTrace S J)
    (a b : ℕ → {u : ℝ // u ∈ S})
    (x y : ℕ → SqueezedState J)
    (hx : ∀ n, x n = .finite (f.1 (a n)) (a n).val ∨
                   x n = .finite (f.2 (a n)) (a n).val)
    (hy : ∀ n, y n = .finite (f.1 (b n)) (b n).val ∨
                   y n = .finite (f.2 (b n)) (b n).val)
    (horder : ∀ n, pairedTraceLE S f (x n) (y n)) :
    ∀ n, (a n).val ≤ (b n).val := by
  intro n
  have hn := horder n
  rcases hx n with hxm | hxp <;> rcases hy n with hym | hyp
  · rw [hxm, hym] at hn
    exact finite_order_time_le f hn
  · rw [hxm, hyp] at hn
    exact finite_order_time_le f hn
  · rw [hxp, hym] at hn
    exact finite_order_time_le f hn
  · rw [hxp, hyp] at hn
    exact finite_order_time_le f hn

private theorem stable_finite_color {C : Type*} [Finite C] (c : ℕ → C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ k : C, ∀ n, c (φ n) = k := by
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber c
  obtain ⟨φ, hφ, hcolor⟩ := Nat.exists_strictMono_subsequence
    (P := fun n => c n = k) (by
      intro N
      obtain ⟨n, hn, hgt⟩ := (Set.infinite_coe_iff.1 hk).exists_gt N
      exact ⟨n, hgt, hn⟩)
  exact ⟨φ, hφ, k, hcolor⟩

private theorem finite_state_limit {α J : Type*} {l : Filter α}
    {v : α → J → ℝ} {t : α → ℝ} {w : J → ℝ} {r : ℝ}
    (hv : Tendsto v l (𝓝 w)) (ht : Tendsto t l (𝓝 r)) :
    Tendsto (fun n => SqueezedState.finite (v n) (t n)) l
      (𝓝 (SqueezedState.finite w r)) := by
  exact (continuous_squeezedState_finite J).continuousAt.tendsto.comp
    (hv.prodMk_nhds ht)

private theorem subtype_left_limit {S : Set ℝ} (a : ℕ → {u : ℝ // u ∈ S})
    (t : {u : ℝ // u ∈ S})
    (ht : Tendsto (fun n => (a n).val) atTop (𝓝 t.val))
    (ha : ∀ n, (a n).val < t.val) :
    Tendsto a atTop (𝓝[Set.Iio t] t) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · exact tendsto_subtype_rng.2 ht
  · exact Filter.Eventually.of_forall (fun n => ha n)

private theorem subtype_right_limit {S : Set ℝ} (a : ℕ → {u : ℝ // u ∈ S})
    (t : {u : ℝ // u ∈ S})
    (ht : Tendsto (fun n => (a n).val) atTop (𝓝 t.val))
    (ha : ∀ n, t.val < (a n).val) :
    Tendsto a atTop (𝓝[Set.Ioi t] t) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · exact tendsto_subtype_rng.2 ht
  · exact Filter.Eventually.of_forall (fun n => ha n)

private theorem compact_ordered_pair_times {S : Set ℝ}
    (a b : ℕ → {u : ℝ // u ∈ S})
    (hab : ∀ n, (a n).val ≤ (b n).val) :
    ∃ (τ υ : EReal) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => ((a (φ n)).val : EReal)) atTop (𝓝 τ) ∧
      Tendsto (fun n => ((b (φ n)).val : EReal)) atTop (𝓝 υ) ∧
      τ ≤ υ := by
  obtain ⟨⟨τ, υ⟩, φ, hφ, hpair⟩ := CompactSpace.tendsto_subseq
    (fun n => (((a n).val : EReal), ((b n).val : EReal)))
  have hτ : Tendsto (fun n => ((a (φ n)).val : EReal)) atTop (𝓝 τ) := by
    simpa [Function.comp_def] using hpair.fst_nhds
  have hυ : Tendsto (fun n => ((b (φ n)).val : EReal)) atTop (𝓝 υ) := by
    simpa [Function.comp_def] using hpair.snd_nhds
  have hle : τ ≤ υ := le_of_tendsto_of_tendsto' hτ hυ (fun n => by
    exact_mod_cast hab (φ n))
  exact ⟨τ, υ, φ, hφ, hτ, hυ, hle⟩

private noncomputable def timeSide (τ : EReal) (t : ℝ) : Ordering :=
  if (t : EReal) < τ then .lt else if (t : EReal) = τ then .eq else .gt

private theorem timeSide_lt {τ : EReal} {t : ℝ}
    (h : timeSide τ t = .lt) : (t : EReal) < τ := by
  by_cases hlt : (t : EReal) < τ
  · exact hlt
  · by_cases heq : (t : EReal) = τ
    · simp [timeSide, heq] at h
    · simp [timeSide, hlt, heq] at h

private theorem timeSide_eq {τ : EReal} {t : ℝ}
    (h : timeSide τ t = .eq) : (t : EReal) = τ := by
  by_cases hlt : (t : EReal) < τ
  · simp [timeSide, hlt] at h
  · by_cases heq : (t : EReal) = τ
    · exact heq
    · simp [timeSide, hlt, heq] at h

private theorem timeSide_gt {τ : EReal} {t : ℝ}
    (h : timeSide τ t = .gt) : τ < (t : EReal) := by
  by_cases hlt : (t : EReal) < τ
  · simp [timeSide, hlt] at h
  · by_cases heq : (t : EReal) = τ
    · simp [timeSide, heq] at h
    · exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)

private theorem finite_trace_color {S : Set ℝ} {J : Type*}
    [DecidableEq (SqueezedState J)]
    (f : RawPairedTrace S J) (a : {u : ℝ // u ∈ S})
    (x : SqueezedState J)
    (hx : x = .finite (f.1 a) a.val ∨ x = .finite (f.2 a) a.val)
    (c : Bool)
    (hc : (if x = .finite (f.1 a) a.val then false else true) = c) :
    x = .finite (if c = true then f.2 a else f.1 a) a.val := by
  classical
  by_cases hm : x = .finite (f.1 a) a.val
  · have hc' : c = false := by simpa [hm] using hc.symm
    simp [hc', hm]
  · have hp : x = .finite (f.2 a) a.val := hx.resolve_left hm
    have hc' : c = true := by simpa [hm] using hc.symm
    simp [hc', hp]

private def chosenTrace {S : Set ℝ} {J : Type*} (f : RawPairedTrace S J)
    (c : Bool) (t : {u : ℝ // u ∈ S}) : J → ℝ :=
  if c = true then f.2 t else f.1 t

private def sideTrace {S : Set ℝ} {J : Type*} (f : RawPairedTrace S J)
    (s : Ordering) (c : Bool) (t : {u : ℝ // u ∈ S}) : J → ℝ :=
  match s with
  | .lt => f.1 t
  | .eq => chosenTrace f c t
  | .gt => f.2 t

private theorem chosen_endpoint_limit {S : Set ℝ} {J : Type*}
    (hS : IsClosed S) (f : RawPairedTrace S J)
    (hleft : ∀ t : {u : ℝ // u ∈ S},
      Tendsto f.1 (𝓝[Set.Iio t] t) (𝓝 (f.1 t)) ∧
      Tendsto f.2 (𝓝[Set.Iio t] t) (𝓝 (f.1 t)))
    (hright : ∀ t : {u : ℝ // u ∈ S},
      Tendsto f.1 (𝓝[Set.Ioi t] t) (𝓝 (f.2 t)) ∧
      Tendsto f.2 (𝓝[Set.Ioi t] t) (𝓝 (f.2 t)))
    (a : ℕ → {u : ℝ // u ∈ S}) (x : ℕ → SqueezedState J)
    (c : Bool) (hx : ∀ n, x n = .finite (chosenTrace f c (a n)) (a n).val)
    (τ : EReal) (side : Ordering)
    (ht : Tendsto (fun n => ((a n).val : EReal)) atTop (𝓝 τ))
    (hs : ∀ n, timeSide τ (a n).val = side) :
    ∃ z : SqueezedState J, Tendsto x atTop (𝓝 z) ∧
      ((τ = ⊥ ∧ z = .bottom) ∨ (τ = ⊤ ∧ z = .top) ∨
        ∃ t : {u : ℝ // u ∈ S},
          τ = (t.val : EReal) ∧ z = .finite (sideTrace f side c t) t.val) := by
  induction τ using EReal.rec with
  | bot =>
      have hbot : Tendsto (fun n => (a n).val) atTop atBot :=
        EReal.tendsto_coe_nhds_bot_iff.mp ht
      have hpole := tendsto_squeezedState_finite_atBot
        (fun n => chosenTrace f c (a n)) (fun n => (a n).val) hbot
      have hconv : Tendsto x atTop (𝓝 (SqueezedState.bottom : SqueezedState J)) := by
        apply Tendsto.congr' ?_ hpole
        exact Filter.Eventually.of_forall (fun n => (hx n).symm)
      exact ⟨.bottom, hconv, Or.inl ⟨rfl, rfl⟩⟩
  | top =>
      have htop : Tendsto (fun n => (a n).val) atTop atTop :=
        EReal.tendsto_coe_nhds_top_iff.mp ht
      have hpole := tendsto_squeezedState_finite_atTop
        (fun n => chosenTrace f c (a n)) (fun n => (a n).val) htop
      have hconv : Tendsto x atTop (𝓝 (SqueezedState.top : SqueezedState J)) := by
        apply Tendsto.congr' ?_ hpole
        exact Filter.Eventually.of_forall (fun n => (hx n).symm)
      exact ⟨.top, hconv, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | coe r =>
      have hreal : Tendsto (fun n => (a n).val) atTop (𝓝 r) :=
        EReal.tendsto_coe.mp ht
      have hrS : r ∈ S := hS.mem_of_tendsto hreal
        (Filter.Eventually.of_forall (fun n => (a n).property))
      let t : {u : ℝ // u ∈ S} := ⟨r, hrS⟩
      cases side with
      | lt =>
          have hlt : ∀ n, (a n).val < t.val := fun n =>
            EReal.coe_lt_coe_iff.mp (timeSide_lt (hs n))
          have ha := subtype_left_limit a t hreal hlt
          have hg : Tendsto (fun n => chosenTrace f c (a n)) atTop (𝓝 (f.1 t)) := by
            cases c with
            | false => simpa [chosenTrace, Function.comp_def] using (hleft t).1.comp ha
            | true => simpa [chosenTrace, Function.comp_def] using (hleft t).2.comp ha
          have hfinite := finite_state_limit hg hreal
          have hconv : Tendsto x atTop (𝓝 (SqueezedState.finite (f.1 t) t.val)) := by
            apply Tendsto.congr' ?_ hfinite
            exact Filter.Eventually.of_forall (fun n => (hx n).symm)
          exact ⟨.finite (f.1 t) t.val, hconv,
            Or.inr (Or.inr ⟨t, rfl, rfl⟩)⟩
      | eq =>
          have hae : ∀ n, a n = t := by
            intro n
            apply Subtype.ext
            exact EReal.coe_injective (timeSide_eq (hs n))
          have hconst : ∀ n, x n = .finite (chosenTrace f c t) t.val := by
            intro n
            simpa [hae n] using hx n
          have hconv : Tendsto x atTop
              (𝓝 (SqueezedState.finite (chosenTrace f c t) t.val)) := by
            apply Tendsto.congr' ?_ tendsto_const_nhds
            exact Filter.Eventually.of_forall (fun n => (hconst n).symm)
          exact ⟨.finite (chosenTrace f c t) t.val, hconv,
            Or.inr (Or.inr ⟨t, rfl, rfl⟩)⟩
      | gt =>
          have hgt : ∀ n, t.val < (a n).val := fun n =>
            EReal.coe_lt_coe_iff.mp (timeSide_gt (hs n))
          have ha := subtype_right_limit a t hreal hgt
          have hg : Tendsto (fun n => chosenTrace f c (a n)) atTop (𝓝 (f.2 t)) := by
            cases c with
            | false => simpa [chosenTrace, Function.comp_def] using (hright t).1.comp ha
            | true => simpa [chosenTrace, Function.comp_def] using (hright t).2.comp ha
          have hfinite := finite_state_limit hg hreal
          have hconv : Tendsto x atTop (𝓝 (SqueezedState.finite (f.2 t) t.val)) := by
            apply Tendsto.congr' ?_ hfinite
            exact Filter.Eventually.of_forall (fun n => (hx n).symm)
          exact ⟨.finite (f.2 t) t.val, hconv,
            Or.inr (Or.inr ⟨t, rfl, rfl⟩)⟩

private theorem sideTrace_in_graph {S : Set ℝ} {J : Type*}
    (f : RawPairedTrace S J) (s : Ordering) (c : Bool)
    (t : {u : ℝ // u ∈ S}) :
    SqueezedState.finite (sideTrace f s c t) t.val ∈ pairedTraceGraph S f := by
  unfold pairedTraceGraph
  right
  right
  refine ⟨t, ?_⟩
  cases s <;> cases c <;> simp [sideTrace, chosenTrace]

private theorem classified_endpoint_in_graph {S : Set ℝ} {J : Type*}
    (f : RawPairedTrace S J) (τ : EReal) (side : Ordering) (c : Bool)
    (z : SqueezedState J)
    (h : (τ = ⊥ ∧ z = .bottom) ∨ (τ = ⊤ ∧ z = .top) ∨
        ∃ t : {u : ℝ // u ∈ S},
          τ = (t.val : EReal) ∧ z = .finite (sideTrace f side c t) t.val) :
    z ∈ pairedTraceGraph S f := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨t, _, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sideTrace_in_graph f side c t

private theorem same_time_minus_plus {S : Set ℝ} {J : Type*}
    (f : RawPairedTrace S J) (t : {u : ℝ // u ∈ S}) :
    pairedTraceLE S f (.finite (f.1 t) t.val) (.finite (f.2 t) t.val) := by
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, rfl, rfl⟩)))

private theorem finite_side_order_of_lt {S : Set ℝ} {J : Type*}
    (f : RawPairedTrace S J)
    (t u : {v : ℝ // v ∈ S})
    (s r : Ordering) (c d : Bool)
    (htu : t.val < u.val) :
    pairedTraceLE S f
      (.finite (sideTrace f s c t) t.val)
      (.finite (sideTrace f r d u) u.val) := by
  exact Or.inr (Or.inr (Or.inr (Or.inl
    ⟨sideTrace f s c t, sideTrace f r d u, t.val, u.val, rfl, rfl, htu⟩)))

private theorem equal_time_side_order {S : Set ℝ} {J : Type*}
    (f : RawPairedTrace S J) (t a b : {u : ℝ // u ∈ S})
    (sa sb : Ordering) (ca cb : Bool)
    (hsa : timeSide (t.val : EReal) a.val = sa)
    (hsb : timeSide (t.val : EReal) b.val = sb)
    (hab : a.val ≤ b.val)
    (horder : pairedTraceLE S f
      (.finite (chosenTrace f ca a) a.val)
      (.finite (chosenTrace f cb b) b.val)) :
    pairedTraceLE S f
      (.finite (sideTrace f sa ca t) t.val)
      (.finite (sideTrace f sb cb t) t.val) := by
  cases sa with
  | lt =>
      cases sb with
      | lt => exact Or.inl (by simp [sideTrace])
      | eq =>
          cases cb with
          | false => exact Or.inl (by simp [sideTrace, chosenTrace])
          | true => simpa [sideTrace, chosenTrace] using same_time_minus_plus f t
      | gt => simpa [sideTrace] using same_time_minus_plus f t
  | eq =>
      cases sb with
      | lt =>
          have hae : a.val = t.val := EReal.coe_injective (timeSide_eq hsa)
          have hbl : b.val < t.val := EReal.coe_lt_coe_iff.mp (timeSide_lt hsb)
          exact False.elim (by linarith)
      | eq =>
          have hae : a = t := Subtype.ext (EReal.coe_injective (timeSide_eq hsa))
          have hbe : b = t := Subtype.ext (EReal.coe_injective (timeSide_eq hsb))
          simpa [hae, hbe, sideTrace] using horder
      | gt =>
          cases ca with
          | false => simpa [sideTrace, chosenTrace] using same_time_minus_plus f t
          | true => exact Or.inl (by simp [sideTrace, chosenTrace])
  | gt =>
      cases sb with
      | lt =>
          have hat : t.val < a.val := EReal.coe_lt_coe_iff.mp (timeSide_gt hsa)
          have hbl : b.val < t.val := EReal.coe_lt_coe_iff.mp (timeSide_lt hsb)
          exact False.elim (by linarith)
      | eq =>
          have hat : t.val < a.val := EReal.coe_lt_coe_iff.mp (timeSide_gt hsa)
          have hbe : b.val = t.val := EReal.coe_injective (timeSide_eq hsb)
          exact False.elim (by linarith)
      | gt => exact Or.inl (by simp [sideTrace])

/-- A sequence of ordered pairs of finite trace states has a convergent
subsequence whose limit remains in the literal ordered-pair graph. The graph,
order, and topology are the frozen `PairedOrderGraph`, `PairedTraceLE`, and
`SqueezedStateTopologicalSpace` definitions. -/
theorem finite_ordered_pair_subsequence
    {S : Set ℝ} {J : Type*} [Countable J]
    (hS : IsClosed S) (f : RawPairedTrace S J)
    (hleft : ∀ t : {u : ℝ // u ∈ S},
      Tendsto f.1 (nhdsWithin t (Set.Iio t)) (nhds (f.1 t)) ∧
      Tendsto f.2 (nhdsWithin t (Set.Iio t)) (nhds (f.1 t)))
    (hright : ∀ t : {u : ℝ // u ∈ S},
      Tendsto f.1 (nhdsWithin t (Set.Ioi t)) (nhds (f.2 t)) ∧
      Tendsto f.2 (nhdsWithin t (Set.Ioi t)) (nhds (f.2 t)))
    (a b : ℕ → {u : ℝ // u ∈ S})
    (x y : ℕ → SqueezedState J)
    (hx : ∀ n, x n = .finite (f.1 (a n)) (a n).val ∨
                   x n = .finite (f.2 (a n)) (a n).val)
    (hy : ∀ n, y n = .finite (f.1 (b n)) (b n).val ∨
                   y n = .finite (f.2 (b n)) (b n).val)
    (horder : ∀ n, pairedTraceLE S f (x n) (y n)) :
    ∃ z ∈ pairedOrderGraph S f, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun n => (x (φ n), y (φ n))) atTop (nhds z) := by
  classical
  -- Literal order at each finite pair puts the first time no later than the second.
  have htime := ordered_finite_times_le f a b x y hx hy horder
  -- Compactify both times as one pair, so both endpoints share the same subsequence.
  obtain ⟨τ, υ, φ, hφ, hτ, hυ, hτυ⟩ := compact_ordered_pair_times a b htime
  -- Stabilize the two trace choices and the side of each limiting time together.
  let color : ℕ → (Bool × Ordering) × (Bool × Ordering) := fun n =>
    ((if x (φ n) = .finite (f.1 (a (φ n))) (a (φ n)).val then false else true,
      timeSide τ (a (φ n)).val),
     (if y (φ n) = .finite (f.1 (b (φ n))) (b (φ n)).val then false else true,
      timeSide υ (b (φ n)).val))
  obtain ⟨ρ, hρ, k, hk⟩ := stable_finite_color color
  let ψ : ℕ → ℕ := fun n => φ (ρ n)
  have hψ : StrictMono ψ := hφ.comp hρ
  have hτψ : Tendsto (fun n => ((a (ψ n)).val : EReal)) atTop (𝓝 τ) := by
    simpa [ψ, Function.comp_def] using hτ.comp hρ.tendsto_atTop
  have hυψ : Tendsto (fun n => ((b (ψ n)).val : EReal)) atTop (𝓝 υ) := by
    simpa [ψ, Function.comp_def] using hυ.comp hρ.tendsto_atTop
  have hcolorX (n : ℕ) :
      (if x (ψ n) = .finite (f.1 (a (ψ n))) (a (ψ n)).val then false else true) =
        k.1.1 := by
    have hc := congrArg (fun p : (Bool × Ordering) × (Bool × Ordering) => p.1.1) (hk n)
    simpa [color, ψ] using hc
  have hcolorY (n : ℕ) :
      (if y (ψ n) = .finite (f.1 (b (ψ n))) (b (ψ n)).val then false else true) =
        k.2.1 := by
    have hc := congrArg (fun p : (Bool × Ordering) × (Bool × Ordering) => p.2.1) (hk n)
    simpa [color, ψ] using hc
  have hsideX (n : ℕ) : timeSide τ (a (ψ n)).val = k.1.2 := by
    have hc := congrArg (fun p : (Bool × Ordering) × (Bool × Ordering) => p.1.2) (hk n)
    simpa [color, ψ] using hc
  have hsideY (n : ℕ) : timeSide υ (b (ψ n)).val = k.2.2 := by
    have hc := congrArg (fun p : (Bool × Ordering) × (Bool × Ordering) => p.2.2) (hk n)
    simpa [color, ψ] using hc
  have hchosenX (n : ℕ) :
      x (ψ n) = .finite (chosenTrace f k.1.1 (a (ψ n))) (a (ψ n)).val := by
    simpa [chosenTrace] using
      finite_trace_color f (a (ψ n)) (x (ψ n)) (hx (ψ n)) k.1.1 (hcolorX n)
  have hchosenY (n : ℕ) :
      y (ψ n) = .finite (chosenTrace f k.2.1 (b (ψ n))) (b (ψ n)).val := by
    simpa [chosenTrace] using
      finite_trace_color f (b (ψ n)) (y (ψ n)) (hy (ψ n)) k.2.1 (hcolorY n)
  -- One-sided trace limits, or pole limits, now determine both state limits.
  obtain ⟨zx, hzx, hclassX⟩ := chosen_endpoint_limit hS f hleft hright
    (fun n => a (ψ n)) (fun n => x (ψ n)) k.1.1 hchosenX τ k.1.2 hτψ hsideX
  obtain ⟨zy, hzy, hclassY⟩ := chosen_endpoint_limit hS f hleft hright
    (fun n => b (ψ n)) (fun n => y (ψ n)) k.2.1 hchosenY υ k.2.2 hυψ hsideY
  -- At coincident finite times, use the original paired order at index zero.
  have hlimitOrder : pairedTraceLE S f zx zy := by
    rcases hclassX with ⟨_, hbotX⟩ | ⟨htopX, htopStateX⟩ |
      ⟨t, hτt, hfiniteX⟩
    · rw [hbotX]
      exact Or.inr (Or.inl rfl)
    · rcases hclassY with ⟨hbotY, _⟩ | ⟨_, htopStateY⟩ |
        ⟨u, hυu, _⟩
      · simp [htopX, hbotY] at hτυ
      · rw [htopStateX, htopStateY]
        exact Or.inl rfl
      · simp [htopX, hυu] at hτυ
    · rcases hclassY with ⟨hbotY, _⟩ | ⟨_, htopStateY⟩ |
        ⟨u, hυu, hfiniteY⟩
      · simp [hτt, hbotY] at hτυ
      · rw [htopStateY]
        exact Or.inr (Or.inr (Or.inl rfl))
      · have htu : t.val ≤ u.val := EReal.coe_le_coe_iff.mp (by
          simpa [hτt, hυu] using hτυ)
        rcases lt_or_eq_of_le htu with hlt | heq
        · rw [hfiniteX, hfiniteY]
          exact finite_side_order_of_lt f t u k.1.2 k.2.2 k.1.1 k.2.1 hlt
        · have htu' : t = u := Subtype.ext heq
          subst u
          rw [hfiniteX, hfiniteY]
          have horderZero : pairedTraceLE S f
              (.finite (chosenTrace f k.1.1 (a (ψ 0))) (a (ψ 0)).val)
              (.finite (chosenTrace f k.2.1 (b (ψ 0))) (b (ψ 0)).val) := by
            simpa only [hchosenX 0, hchosenY 0] using horder (ψ 0)
          apply equal_time_side_order f t (a (ψ 0)) (b (ψ 0))
            k.1.2 k.2.2 k.1.1 k.2.1
          · simpa [hτt] using hsideX 0
          · simpa [hυu] using hsideY 0
          · exact htime (ψ 0)
          · exact horderZero
  refine ⟨(zx, zy), ?_, ψ, hψ, ?_⟩
  · change zx ∈ pairedTraceGraph S f ∧ zy ∈ pairedTraceGraph S f ∧
      pairedTraceLE S f zx zy
    exact ⟨classified_endpoint_in_graph f τ k.1.2 k.1.1 zx hclassX,
      classified_endpoint_in_graph f υ k.2.2 k.2.1 zy hclassY, hlimitOrder⟩
  · exact hzx.prodMk_nhds hzy

end LPP.Busemann
