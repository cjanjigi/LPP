/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.StaircaseGeneral
public import Differentiability.Model.StaircaseFamilyIndex
public import LPP_Foundations.Model.Paths.HorizontalFirst
import Mathlib.Tactic

/-!
# The staircase event for a finite family of paths

Apply Lemma B.6 of the differentiability preprint to the family in Section B.3,
item (C5). Labels `(c, z, u, p, n)` describe forward segments (`c = 0`), backward
segments (`1`), arrival paths (`2`) and greedy paths to a target level (`3`).
Each member is its stream of collected vertices, determined by the very-bad
mask; `staircase_general_family_tendsto` with `q = 11` gives the limit.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Filter
open scoped Topology BigOperators Classical ENNReal

namespace LPPDifferentiability

private abbrev Idx := ℕ × Lattice × Lattice × ℕ × ℕ
private noncomputable def maskOf (T : ℝ) (ω : Environment) : Lattice → Bool :=
  fun z => if ω z < -T then true else false

private theorem maskOf_false (T : ℝ) (ω : Environment) (z : Lattice) :
    maskOf T ω z = false ↔ -T ≤ ω z := by
  unfold maskOf
  by_cases h : ω z < -T
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

private theorem maskOf_true (T : ℝ) (ω : Environment) (z : Lattice) :
    maskOf T ω z = true ↔ ω z < -T := by
  unfold maskOf; by_cases h : ω z < -T <;> simp [h]
private def reachM (b : Lattice → Bool) (y : Lattice) : Set Lattice :=
  {y' | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = y' ∧
    ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → b (q.vertex i) = false}
private def reachBackM (b : Lattice → Bool) (z : Lattice) : Set Lattice :=
  {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
    ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → b (q.vertex i) = false}
private def Vf (b : Lattice → Bool) : Set Lattice := {y | (reachM b y).Finite}
private def Wf (b : Lattice → Bool) : Set Lattice :=
  {y | b (-y) = true ∨ (reachBackM b (-y)).Finite}

private theorem hWf (y : Lattice) : MeasurableSet {b : Lattice → Bool | y ∈ Wf b} :=
  (show MeasurableSet ((fun b : Lattice → Bool => b (-y)) ⁻¹' {true}) from
    (measurable_pi_apply (-y)) (measurableSet_singleton true)).union
    (measurableSet_reachBack_finite (-y))
private def arrN (z v : Lattice) : ℕ := (v.1 - z.1 + (v.2 - z.2)).toNat
private noncomputable def arrX (V : Set Lattice) (z v : Lattice) : ℕ → Lattice :=
  GreedyAttachment.vertex z (((v.1 - z.1 : ℤ) : ℝ) / (arrN z v : ℝ)) V
private noncomputable abbrev arrZ (V : Set Lattice) (z v : Lattice) (L : ℕ) : Lattice :=
  arrX V z v (arrN z v - L)
private noncomputable abbrev arrE (V : Set Lattice) (z v : Lattice) (L : ℕ) : ℕ × ℕ :=
  ((v.1 - (arrZ V z v L).1).toNat, (v.2 - (arrZ V z v L).2).toNat)
private noncomputable abbrev arrH (V : Set Lattice) (z v : Lattice) (L : ℕ) :=
  horizontalFirst (arrZ V z v L) (arrE V z v L)
private def hfV (x v : Lattice) (t : ℕ) : Lattice :=
  (x.1 + ((min t (v.1 - x.1).toNat : ℕ) : ℤ), x.2 + ((t - (v.1 - x.1).toNat : ℕ) : ℤ))
private noncomputable def arrS (L : ℕ) (V : Set Lattice) (z v : Lattice) (s : ℕ) : Lattice :=
  if s < arrN z v - L then arrX V z v s else hfV (arrZ V z v L) v (s - (arrN z v - L))
private noncomputable def q4 (a : ℝ) (W0 : ℕ) (z u : Lattice) (Λ : ℤ) : ℝ :=
  ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - 2 * (W0 : ℝ) - 3 + a * (Λ : ℝ) - (z.1 : ℝ)) /
    ((Λ - (z.1 + z.2) : ℤ) : ℝ)
private noncomputable def stream (a : ℝ) (W0 L : ℕ) (b : Lattice → Bool) : Idx → ℕ → Lattice
  | (0, z, _, p, _), s => GreedyAttachment.vertex z a (Vf b) (p + s)
  | (1, z, _, p, _), s => -GreedyAttachment.vertex (-z) a (Wf b) (p + 1 + s)
  | (2, z, v, _, _), s => arrS L (Vf b) z v s
  | (3, z, u, p, _), s => GreedyAttachment.vertex z (q4 a W0 z u (z.1 + z.2 + (p : ℤ))) (Vf b) s
  | _, s => ((s : ℤ), 0)
private abbrev CoreEv (a : ℝ) (W0 L : ℕ) (Cm T tk Nl : ℝ) (Qf : Finset Lattice)
    (ω : Environment) (t : Idx) : Prop :=
  (t.2.2.2.2 : ℝ) ≤ Nl ∧
    (∀ i < t.2.2.2.2, maskOf T ω (stream a W0 L (maskOf T ω) t i) = false ∧
      stream a W0 L (maskOf T ω) t i ∈ Qf) ∧
    ∑ i ∈ Finset.range t.2.2.2.2, ω (stream a W0 L (maskOf T ω) t i) <
      -2 * Cm * (t.2.2.2.2 : ℝ) - tk / 2

private theorem arrS_level (L : ℕ) (V : Set Lattice) (z v : Lattice) (s : ℕ) :
    (arrS L V z v s).1 + (arrS L V z v s).2 = z.1 + z.2 + (s : ℤ) := by
  unfold arrS
  split_ifs with h
  · exact GreedyAttachment.level _ _ _ _
  · have hl : (arrZ V z v L).1 + (arrZ V z v L).2 = z.1 + z.2 + ((arrN z v - L : ℕ) : ℤ) :=
      GreedyAttachment.level _ _ _ _
    simp only [hfV, Nat.cast_min]
    omega

private theorem vertex_inj (u : Lattice) (q : ℝ) (V : Set Lattice) (m m' : ℕ)
    (h : GreedyAttachment.vertex u q V m = GreedyAttachment.vertex u q V m') : m = m' := by
  have h1 := GreedyAttachment.level u q V m
  have h2 := GreedyAttachment.level u q V m'
  rw [h] at h1
  omega

private theorem stream_injective (a : ℝ) (W0 L : ℕ) (b : Lattice → Bool) (t : Idx) :
    Function.Injective (stream a W0 L b t) := by
  rcases t with ⟨_ | _ | _ | _ | c, z, u, p, n⟩
  · intro s s' h
    have := vertex_inj z a (Vf b) (p + s) (p + s') h
    omega
  · intro s s' h
    have h' : -GreedyAttachment.vertex (-z) a (Wf b) (p + 1 + s) =
        -GreedyAttachment.vertex (-z) a (Wf b) (p + 1 + s') := h
    have := vertex_inj (-z) a (Wf b) _ _ (neg_inj.1 h')
    omega
  · intro s s' h
    have h1 := arrS_level L (Vf b) z u s
    have h2 := arrS_level L (Vf b) z u s'
    rw [show arrS L (Vf b) z u s = arrS L (Vf b) z u s' from h] at h1
    omega
  · intro s s' h
    exact vertex_inj z (q4 a W0 z u (z.1 + z.2 + (p : ℤ))) (Vf b) s s' h
  · intro s s' h
    have h' : ((s : ℤ), (0 : ℤ)) = ((s' : ℤ), (0 : ℤ)) := h
    simpa using h'

private theorem measurable_stream (a : ℝ) (W0 L : ℕ) (t : Idx) (s : ℕ) :
    Measurable (fun b : Lattice → Bool => stream a W0 L b t s) := by
  rcases t with ⟨_ | _ | _ | _ | c, z, u, p, n⟩
  · exact measurable_greedy_vertex z a Vf measurableSet_reach_finite (p + s)
  · exact (measurable_of_countable (fun w : Lattice => -w)).comp
      (measurable_greedy_vertex (-z) a Wf hWf (p + 1 + s))
  · show Measurable fun b : Lattice → Bool => arrS L (Vf b) z u s
    unfold arrS
    by_cases h : s < arrN z u - L
    · simp only [h, ↓reduceIte]
      exact measurable_greedy_vertex z _ Vf measurableSet_reach_finite s
    · simp only [h, ↓reduceIte]
      exact (measurable_of_countable (fun x => hfV x u (s - (arrN z u - L)))).comp
        (measurable_greedy_vertex z _ Vf measurableSet_reach_finite _)
  · exact measurable_greedy_vertex z _ Vf measurableSet_reach_finite s
  · show Measurable (fun _ : Lattice → Bool => ((s : ℤ), (0 : ℤ)))
    exact measurable_const

private theorem idx_le (Lvl : ℝ) (x y : Lattice) (m' : ℕ) (hx : |((x.1 + x.2 : ℤ) : ℝ)| ≤ Lvl)
    (hy : |((y.1 + y.2 : ℤ) : ℝ)| ≤ Lvl)
    (h : y.1 + y.2 = x.1 + x.2 + (m' : ℤ) ∨ y.1 + y.2 = x.1 + x.2 - (m' : ℤ)) :
    m' ≤ ⌊2 * Lvl⌋₊ := by
  refine Nat.le_floor ?_
  rw [abs_le] at hx hy
  rcases h with h | h
  · have : ((y.1 + y.2 : ℤ) : ℝ) = ((x.1 + x.2 : ℤ) : ℝ) + m' := by exact_mod_cast h
    linarith [hx.1, hx.2, hy.1, hy.2]
  · have : ((y.1 + y.2 : ℤ) : ℝ) = ((x.1 + x.2 : ℤ) : ℝ) - m' := by exact_mod_cast h
    linarith [hx.1, hx.2, hy.1, hy.2]

private theorem w2 (a : ℝ) (W0 L : ℕ) (Cm T tk Nl : ℝ) (Qs : Set Lattice) (Qf : Finset Lattice)
    (J : Finset Idx) (hcov : ∀ z ∈ Qs, z ∈ Qf)
    (hJ : ∀ z ∈ Qf, ∀ v ∈ Qf, ∀ n ≤ ⌊Nl⌋₊, (2, z, v, 0, n) ∈ J) (ω : Environment)
    (V : Set Lattice) (hV : V = Vf (maskOf T ω)) (z v : Lattice) (hz1 : z.1 ≤ v.1)
    (hz2 : z.2 ≤ v.2) (hLn : L ≤ arrN z v) (hnl : (arrN z v : ℝ) ≤ Nl)
    (hx1 : (arrZ V z v L).1 ≤ v.1) (hx2 : (arrZ V z v L).2 ≤ v.2)
    (hxQ : ∀ s ≤ arrN z v - L, arrX V z v s ∈ Qs)
    (hhQ : ∀ i : Fin ((arrE V z v L).1 + (arrE V z v L).2 + 1), (arrH V z v L).vertex i ∈ Qs)
    (hxT : ∀ s < arrN z v - L, -T ≤ ω (arrX V z v s))
    (hhT : ∀ i : Fin ((arrE V z v L).1 + (arrE V z v L).2 + 1),
      i.val < (arrE V z v L).1 + (arrE V z v L).2 → -T ≤ ω ((arrH V z v L).vertex i))
    (hlt : (∑ s ∈ Finset.range (arrN z v - L), ω (arrX V z v s)) + pathWeight ω (arrH V z v L) <
      -2 * Cm * (arrN z v : ℝ) - tk / 2) :
    ∃ t ∈ J, CoreEv a W0 L Cm T tk Nl Qf ω t := by
  subst hV
  set M := Vf (maskOf T ω)
  have hn : arrN z v = (v.1 - z.1 + (v.2 - z.2)).toNat := rfl
  have hl : (arrZ M z v L).1 + (arrZ M z v L).2 = z.1 + z.2 + ((arrN z v - L : ℕ) : ℤ) :=
    GreedyAttachment.level _ _ _ _
  have e1 : (arrE M z v L).1 = (v.1 - (arrZ M z v L).1).toNat := rfl
  have e2 : (arrE M z v L).2 = (v.2 - (arrZ M z v L).2).toNat := rfl
  have he : (arrE M z v L).1 + (arrE M z v L).2 = L := by omega
  have hvQ : v ∈ Qs := by
    have h := hhQ (Fin.last _)
    rwa [(arrH M z v L).finish, show arrZ M z v L + (((arrE M z v L).1 : ℤ), ((arrE M z v L).2 : ℤ))
        = v from Prod.ext (by show (arrZ M z v L).1 + ((arrE M z v L).1 : ℤ) = v.1; omega)
          (by show (arrZ M z v L).2 + ((arrE M z v L).2 : ℤ) = v.2; omega)] at h
  have hz : z ∈ Qs := hxQ 0 (Nat.zero_le _)
  refine ⟨(2, z, v, 0, arrN z v), hJ z (hcov z hz) v (hcov v hvQ) _ (Nat.le_floor hnl), hnl,
    fun s hs => ?_, ?_⟩
  · have hs' : s < arrN z v := hs
    show maskOf T ω (arrS L M z v s) = false ∧ arrS L M z v s ∈ Qf
    unfold arrS
    split_ifs with h
    · exact ⟨(maskOf_false _ _ _).2 (hxT s h), hcov _ (hxQ s h.le)⟩
    · exact ⟨(maskOf_false _ _ _).2 (hhT ⟨s - (arrN z v - L), by omega⟩
        (by show s - (arrN z v - L) < _; omega)), hcov _ (hhQ ⟨s - (arrN z v - L), by omega⟩)⟩
  · have hpw : pathWeight ω (arrH M z v L) = ∑ s ∈ Finset.range L, ω (hfV (arrZ M z v L) v s) :=
      (Fin.sum_univ_eq_sum_range (fun s => ω (hfV (arrZ M z v L) v s))
        ((arrE M z v L).1 + (arrE M z v L).2)).trans (by rw [he])
    have hsum : ∑ s ∈ Finset.range (arrN z v), ω (arrS L M z v s) =
        (∑ s ∈ Finset.range (arrN z v - L), ω (arrX M z v s)) + pathWeight ω (arrH M z v L) := by
      rw [hpw]
      calc _ = ∑ s ∈ Finset.range ((arrN z v - L) + L), ω (arrS L M z v s) := by
            rw [Nat.sub_add_cancel hLn]
        _ = _ := by
          rw [Finset.sum_range_add]
          congr 1
          · exact Finset.sum_congr rfl fun s hs => by
              simp only [arrS, Finset.mem_range.1 hs, ↓reduceIte]
          · refine Finset.sum_congr rfl fun s _ => ?_
            have hh : ¬ (arrN z v - L + s < arrN z v - L) := by omega
            simp only [arrS, hh, ↓reduceIte, Nat.add_sub_cancel_left]
    show ∑ s ∈ Finset.range (arrN z v), ω (arrS L M z v s) < -2 * Cm * (arrN z v : ℝ) - tk / 2
    rw [hsum]
    exact hlt

theorem staircase_family_event_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ] (p' : ℝ) (hp' : 1 < p')
    (hmom : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (A B ε₀ : ℝ) (hA : 0 < A) (_ : 0 < B)
    (hε₀ : 0 < ε₀) (m1 K1 K2 : ℕ) (_ : 1 ≤ m1) (_ : 1 ≤ K1) (_ : 1 ≤ K2)
    (hK2p : 24 < (K2 : ℝ) * (p' - 1))
    (k0 : ℕ) (m : ℕ → ℕ) (hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k) :
  let θ₁ : ℝ := min a (1 - a) / 5
  let cstar : ℝ := 50 / min a (1 - a)
  let Cm : ℝ := ∫ x : ℝ, max (-x) 0 ∂μ
  let reach : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let reachBack : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let Ntr : ℕ := K1 * (2 * m1 ^ 2 + 1) ^ 2
  let W0 : ℕ := Ntr + 1
  let L : ℕ := ⌈4 * ((W0 : ℝ) + 2) / θ₁⌉₊
  let Qk : ℕ → Set Lattice := fun k =>
    {z | |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k ∧
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ B * (2 : ℝ) ^ k}
  let Tk : ℕ → ℝ := fun k => ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K2 : ℝ))
  let Estair : Environment → ℕ → Prop := fun ω k =>
    let T : ℝ := Tk k
    let t : ℝ := ε₀ * (2 : ℝ) ^ k / (k : ℝ)
    let Nl : ℝ := 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k
    let Vb : Set Lattice := {y | (reach ω T y).Finite}
    let Wb : Set Lattice := {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite}
    (∀ (u : Lattice) (i n : ℕ), (n : ℝ) ≤ Nl →
      (∀ s, s ≤ i + n → GreedyAttachment.vertex u a Vb s ∈ Qk k) →
      (∀ s, s < n → -T ≤ ω (GreedyAttachment.vertex u a Vb (i + s))) →
      -2 * Cm * (n : ℝ) - t / 2 ≤
        ∑ s ∈ Finset.range n, ω (GreedyAttachment.vertex u a Vb (i + s))) ∧
    (∀ (u : Lattice) (i n : ℕ), (n : ℝ) ≤ Nl →
      (∀ s, s ≤ i + n → -GreedyAttachment.vertex (-u) a Wb s ∈ Qk k) →
      (∀ s, s < n → -T ≤ ω (-GreedyAttachment.vertex (-u) a Wb (i + 1 + s))) →
      -2 * Cm * (n : ℝ) - t / 2 ≤
        ∑ s ∈ Finset.range n, ω (-GreedyAttachment.vertex (-u) a Wb (i + 1 + s))) ∧
    (∀ z v : Lattice, z.1 ≤ v.1 → z.2 ≤ v.2 →
      let n : ℕ := (v.1 - z.1 + (v.2 - z.2)).toNat
      let q : ℝ := ((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ)
      let x : ℕ → Lattice := GreedyAttachment.vertex z q Vb
      let e : ℕ × ℕ := ((v.1 - (x (n - L)).1).toNat, (v.2 - (x (n - L)).2).toNat)
      L ≤ n → (n : ℝ) ≤ Nl → (x (n - L)).1 ≤ v.1 → (x (n - L)).2 ≤ v.2 →
      (∀ s, s ≤ n - L → x s ∈ Qk k) →
      (∀ i : Fin (e.1 + e.2 + 1), (horizontalFirst (x (n - L)) e).vertex i ∈ Qk k) →
      (∀ s, s < n - L → -T ≤ ω (x s)) →
      (∀ i : Fin (e.1 + e.2 + 1), i.val < e.1 + e.2 →
        -T ≤ ω ((horizontalFirst (x (n - L)) e).vertex i)) →
      -2 * Cm * (n : ℝ) - t / 2 ≤
        (∑ s ∈ Finset.range (n - L), ω (x s)) +
          pathWeight ω (horizontalFirst (x (n - L)) e)) ∧
    (∀ (z u : Lattice) (Λ : ℤ) (n : ℕ), z.1 + z.2 < Λ →
      ((Λ - (z.1 + z.2) : ℤ) : ℝ) ≤ Nl → (n : ℝ) ≤ Nl → u ∈ Qk k →
      let q : ℝ := ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - 2 * (W0 : ℝ) - 3 +
        a * (Λ : ℝ) - (z.1 : ℝ)) / ((Λ - (z.1 + z.2) : ℤ) : ℝ)
      (∀ s, s ≤ n → GreedyAttachment.vertex z q Vb s ∈ Qk k) →
      (∀ s, s < n → -T ≤ ω (GreedyAttachment.vertex z q Vb s)) →
      -2 * Cm * (n : ℝ) - t / 2 ≤
        ∑ s ∈ Finset.range n, ω (GreedyAttachment.vertex z q Vb s))
  Tendsto (fun k : ℕ => (environmentLaw μ).real {ω : Environment | ¬ Estair ω k})
    atTop (𝓝 0) := by
  classical
  intro _ cstar Cm reach reachBack _ W0 L Qk Tk Estair
  have hcpos : 0 < cstar := div_pos (by norm_num) (lt_min ha₀ (by linarith))
  obtain ⟨k1, -, Qf, F, hF⟩ := exists_staircase_region_index a A B cstar hA hcpos k0 m hm3
  have hCm : 0 ≤ Cm := integral_nonneg fun y => le_max_right _ _
  have hcov : ∀ k, k1 ≤ k → ∀ z ∈ Qk k, z ∈ Qf k := fun k hk z hz => (hF k hk).1 z hz.1 hz.2
  have hS2 : ∀ k, ∀ x ∈ Qk k, ∀ y ∈ Qk k, ∀ m' : ℕ, (y.1 + y.2 = x.1 + x.2 + (m' : ℤ) ∨
      y.1 + y.2 = x.1 + x.2 - (m' : ℤ)) → m' ≤ ⌊2 * (A + 5) * (2 : ℝ) ^ m k⌋₊ :=
    fun k x hx y hy m' h => by
      have := idx_le ((A + 5) * (2 : ℝ) ^ m k) x y m' hx.1 hy.1 h
      rwa [← mul_assoc] at this
  have hVeq : ∀ (ω : Environment) (k : ℕ),
      {y | (reach ω (Tk k) y).Finite} = Vf (maskOf (Tk k) ω) := fun ω k => by
    ext y; simp only [reach, Vf, reachM, Set.mem_ofPred_eq, maskOf_false]
  have hWeq : ∀ (ω : Environment) (k : ℕ),
      {y | ω (-y) < -Tk k ∨ (reachBack ω (Tk k) (-y)).Finite} = Wf (maskOf (Tk k) ω) :=
    fun ω k => by
      ext y; simp only [reachBack, Wf, reachBackM, Set.mem_ofPred_eq, maskOf_false, maskOf_true]
  obtain ⟨act, hact⟩ : ∃ act : ∀ k, (Lattice → Bool) → ↥(F k) → Bool, ∀ k b j,
      act k b j = true ↔ ((k1 ≤ k ∧ ((j.1.2.2.2.2 : ℕ) : ℝ) ≤
          8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k) ∧
        ∀ i < j.1.2.2.2.2, b (stream a W0 L b j.1 i) = false ∧ stream a W0 L b j.1 i ∈ Qf k) :=
    ⟨fun k b j => decide _, fun k b j => decide_eq_true_iff⟩
  obtain ⟨sit, hsit⟩ : ∃ sit : ∀ k, (Lattice → Bool) → ↥(F k) → Finset Lattice, ∀ k b j,
      sit k b j = (Finset.range j.1.2.2.2.2).image (stream a W0 L b j.1) :=
    ⟨fun k b j => (Finset.range j.1.2.2.2.2).image (stream a W0 L b j.1), fun _ _ _ => rfl⟩
  have hmeas : ∀ k (j : ↥(F k)) (s : Finset Lattice),
      MeasurableSet {b : Lattice → Bool | act k b j = true ∧ sit k b j = s} := by
    intro k j s
    by_cases hc : k1 ≤ k ∧ ((j.1.2.2.2.2 : ℕ) : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k
    · have e : {b : Lattice → Bool | act k b j = true ∧ sit k b j = s} =
          {b | (∀ i < j.1.2.2.2.2, b (stream a W0 L b j.1 i) = false ∧
              stream a W0 L b j.1 i ∈ Qf k) ∧
            (Finset.range j.1.2.2.2.2).image (fun i => stream a W0 L b j.1 i) = s} :=
        Set.ext fun b => by simp [hact, hsit, hc]
      rw [e]
      exact measurableSet_stream_family (fun i b => stream a W0 L b j.1 i)
        (fun i => measurable_stream a W0 L j.1 i) _ _ s
    · have e : {b : Lattice → Bool | act k b j = true ∧ sit k b j = s} = ∅ :=
        Set.ext fun b => by simp [hact, hc]
      rw [e]; exact MeasurableSet.empty
  have hmain : Tendsto (fun k : ℕ => (environmentLaw μ).real {ω : Environment |
      ∃ j : ↥(F k), act k (maskOf (Tk k) ω) j = true ∧ ∑ z ∈ sit k (maskOf (Tk k) ω) j, ω z <
        -2 * Cm * ((sit k (maskOf (Tk k) ω) j).card : ℝ) - ε₀ * (2 : ℝ) ^ k / (k : ℝ) / 2})
      atTop (𝓝 0) :=
    staircase_general_family_tendsto μ p' hp' hmom ε₀ cstar 11 hε₀ hcpos (by norm_num) K2
      (by linarith) k1 (fun k => (Qf k : Set Lattice)) (fun k => (Qf k).finite_toSet)
      (fun k => ↥(F k))
      (fun k hk => by
        rw [Fintype.card_coe, show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        exact (hF k hk).2.1)
      act sit
      (fun k b j h => le_trans (by
        rw [hsit]; exact_mod_cast Finset.card_image_le.trans (Finset.card_range _).le)
        ((hact k b j).1 h).1.2)
      (fun k b j h z hz => by
        rw [hsit] at hz
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
        exact (((hact k b j).1 h).2 i (Finset.mem_range.1 hi)).2)
      (fun k b j h z hz => by
        rw [hsit] at hz
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
        exact (((hact k b j).1 h).2 i (Finset.mem_range.1 hi)).1)
      hmeas
  have hincl : ∀ k, k1 ≤ k → ∀ ω : Environment, ¬ Estair ω k → ∃ t ∈ F k,
      CoreEv a W0 L Cm (Tk k) (ε₀ * (2 : ℝ) ^ k / (k : ℝ))
        (8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k) (Qf k) ω t := by
    intro k hk ω hω
    by_contra hno
    apply hω
    simp only [Estair]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u i n hn hQ hT
      by_contra hlt
      rw [not_le, hVeq ω k] at hlt
      rw [hVeq ω k] at hQ hT
      have hu : u ∈ Qk k := hQ 0 (Nat.zero_le _)
      exact hno ⟨(0, u, (0, 0), i, n), ((hF k hk).2.2.1 u (hcov k hk u hu) i
        (le_trans (Nat.le_add_right i n) (hS2 k u hu _ (hQ (i + n) le_rfl) (i + n)
          (Or.inl (GreedyAttachment.level u a _ (i + n))))) n (Nat.le_floor hn)).1, hn,
        fun s hs => ⟨(maskOf_false _ _ _).2 (hT s hs), hcov k hk _ (hQ (i + s) (by have h' : s < n := hs; omega))⟩, hlt⟩
    · intro u i n hn hQ hT
      by_contra hlt
      rw [not_le, hWeq ω k] at hlt
      rw [hWeq ω k] at hQ hT
      have hu : u ∈ Qk k := by simpa using hQ 0 (Nat.zero_le _)
      have hi : i ≤ ⌊2 * (A + 5) * (2 : ℝ) ^ m k⌋₊ := by
        refine le_trans (Nat.le_add_right i n) (hS2 k u hu _ (hQ (i + n) le_rfl) (i + n)
          (Or.inr ?_))
        have := GreedyAttachment.level (-u) a (Wf (maskOf (Tk k) ω)) (i + n)
        simp only [Prod.fst_neg, Prod.snd_neg] at this ⊢
        omega
      exact hno ⟨(1, u, (0, 0), i, n),
        ((hF k hk).2.2.1 u (hcov k hk u hu) i hi n (Nat.le_floor hn)).2, hn,
        fun s hs => ⟨(maskOf_false _ _ _).2 (hT s hs),
          hcov k hk _ (hQ (i + 1 + s) (by have h' : s < n := hs; omega))⟩, hlt⟩
    · intro z v hz1 hz2 hLn hnl hx1 hx2 hxQ hhQ hxT hhT
      by_contra hlt
      rw [not_le] at hlt
      exact hno (w2 a W0 L Cm _ _ _ _ _ _ (hcov k hk) (hF k hk).2.2.2.1 ω _ (hVeq ω k) z v hz1 hz2
        hLn hnl hx1 hx2 hxQ hhQ hxT hhT hlt)
    · intro z u Λ n hzΛ hdl hnl huQ hQ hT
      by_contra hlt
      rw [not_le, hVeq ω k] at hlt
      rw [hVeq ω k] at hQ hT
      obtain ⟨d, rfl⟩ : ∃ d : ℕ, Λ = z.1 + z.2 + (d : ℤ) :=
        ⟨(Λ - (z.1 + z.2)).toNat, by omega⟩
      have hd : (d : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k := by
        have : ((z.1 + z.2 + (d : ℤ) - (z.1 + z.2) : ℤ) : ℝ) = (d : ℝ) := by push_cast; ring
        rwa [this] at hdl
      exact hno ⟨(3, z, u, d, n), (hF k hk).2.2.2.2 z (hcov k hk z (hQ 0 (Nat.zero_le _))) u
        (hcov k hk u huQ) d (Nat.le_floor hd) n (Nat.le_floor hnl), hnl,
        fun s hs => ⟨(maskOf_false _ _ _).2 (hT s hs), hcov k hk _ (hQ s hs.le)⟩, hlt⟩
  refine squeeze_zero' (Eventually.of_forall fun k => measureReal_nonneg) ?_ hmain
  filter_upwards [eventually_ge_atTop k1] with k hk
  refine measureReal_mono (fun ω hω => ?_)
  obtain ⟨t, ht, hn, hY, hlt⟩ := hincl k hk ω hω
  show ∃ j : ↥(F k), act k (maskOf (Tk k) ω) j = true ∧ _
  refine ⟨⟨t, ht⟩, (hact k _ _).2 ⟨⟨hk, hn⟩, hY⟩, ?_⟩
  have hc : (((Finset.range t.2.2.2.2).image (stream a W0 L (maskOf (Tk k) ω) t)).card : ℝ) ≤
      (t.2.2.2.2 : ℝ) := by
    exact_mod_cast Finset.card_image_le.trans (Finset.card_range _).le
  rw [hsit, Finset.sum_image (stream_injective a W0 L _ t).injOn]
  have := mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℝ) ≤ 2 * Cm)
  linarith

end LPPDifferentiability
