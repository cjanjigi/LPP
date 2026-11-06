/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.StairGreedyForward
public import LPP_Foundations.Model.Paths.Split
import Mathlib.Tactic

/-! # Backward greedy paths avoiding `V ∪ V̄←` (item (ii) of Lemma B.5, backward)

The backward path from `z` is the reflection `y ↦ -y` of the forward greedy recursion for the
avoided set `Wb = {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite}`. The deterministic core
`stair_greedy_core` is applied to the reflected set, region and chain; the reflection is applied
to the construction only, so the collected-vertex convention of the reachable sets is unchanged. -/

public section

namespace LPPDifferentiability

private abbrev reachBackSet (ω : Environment) (T : ℝ) (z : Lattice) : Set Lattice :=
  {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
    ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}

private theorem reachBack_of_vertex (ω : Environment) (T : ℝ) {y : Lattice} {d : ℕ × ℕ}
    (q : Path y d) (hq : ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i))
    (k : Fin (d.1 + d.2 + 1)) (hk : k.val < d.1 + d.2) :
    -T ≤ ω (q.vertex k) ∧ y ∈ reachBackSet ω T (q.vertex k) := by
  refine ⟨hq k hk, q.splitDisplacement k, q.prefixPath k, (q.split_vertex k).symm, fun i hi => ?_⟩
  have hl := q.splitDisplacement_length k
  exact hq ⟨i.val, by omega⟩ (by show i.val < _; omega)

/-- A site whose two predecessors are very bad or have finite backward sets has a finite
backward reachable set. -/
private theorem reachBack_finite_of_pred (ω : Environment) (T : ℝ) (x : Lattice)
    (h1 : ω (x - (1, 0)) < -T ∨ (reachBackSet ω T (x - (1, 0))).Finite)
    (h2 : ω (x - (0, 1)) < -T ∨ (reachBackSet ω T (x - (0, 1))).Finite) :
    (reachBackSet ω T x).Finite := by
  have hB : ∀ a : Lattice, (ω a < -T ∨ (reachBackSet ω T a).Finite) →
      {y | -T ≤ ω a ∧ y ∈ reachBackSet ω T a}.Finite := by
    rintro a (h | h)
    · exact Set.finite_empty.subset fun y hy => absurd hy.1 (not_le.mpr h)
    · exact h.subset fun y hy => hy.2
  refine (((Set.finite_singleton x).union (hB _ h1)).union (hB _ h2)).subset ?_
  rintro w ⟨d, q, hw, hq⟩
  by_cases hd : d.1 + d.2 = 0
  · rw [show d.1 = 0 by omega, show d.2 = 0 by omega] at hw
    exact Or.inl (Or.inl (show w = x by rw [← hw]; apply Prod.ext <;> simp))
  · have hk : d.1 + d.2 - 1 < d.1 + d.2 := by omega
    have hs : x = q.vertex ⟨d.1 + d.2 - 1, by omega⟩ + (1, 0) ∨
        x = q.vertex ⟨d.1 + d.2 - 1, by omega⟩ + (0, 1) := by
      have hst := q.step ⟨d.1 + d.2 - 1, hk⟩
      rw [show (⟨d.1 + d.2 - 1, hk⟩ : Fin (d.1 + d.2)).succ = Fin.last (d.1 + d.2) from
        Fin.ext (by simp; omega), q.finish, hw] at hst
      exact hst
    obtain ⟨hg, hmem⟩ := reachBack_of_vertex ω T q hq ⟨d.1 + d.2 - 1, by omega⟩ hk
    rcases hs with h | h <;> rw [eq_sub_of_add_eq h.symm] at hg hmem
    · exact Or.inl (Or.inr (And.intro hg hmem))
    · exact Or.inr (And.intro hg hmem)

private theorem l1_neg (a b : Lattice) :
    |(-a).1 - (-b).1| + |(-a).2 - (-b).2| = |a.1 - b.1| + |a.2 - b.2| := by
  simp only [Prod.fst_neg, Prod.snd_neg, neg_sub_neg]
  rw [abs_sub_comm b.1 a.1, abs_sub_comm b.2 a.2]

/-- **Backward greedy path** (item (ii) of Lemma B.5). -/
theorem stair_greedy_backward (ω : Environment) (T θ₁ : ℝ) (m1 K1 : ℕ) (Q : Set Lattice) :
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
  let Wb : Set Lattice := {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite}
  0 < θ₁ → θ₁ ≤ 1 / 10 → 1 ≤ m1 → 1 ≤ K1 → Egeo ω T Q →
  ∀ z ∈ Q, -T ≤ ω z → ¬ (reachBack ω T z).Finite → ∀ q : ℝ, θ₁ ≤ q → q ≤ 1 - θ₁ →
    ∀ n : ℕ, (∀ i, i ≤ n → -GreedyAttachment.vertex (-z) q Wb i ∈ Q) →
    ∀ i, i ≤ n →
      -T ≤ ω (-GreedyAttachment.vertex (-z) q Wb i) ∧
      ¬ (reachBack ω T (-GreedyAttachment.vertex (-z) q Wb i)).Finite ∧
      |GreedyAttachment.deviation (-z) q i (GreedyAttachment.vertex (-z) q Wb i)| ≤ (W0 : ℝ) := by
  intro reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo Wb hθ hθ' hm hK hE z _ hzT hzB q hq1 hq2 n
    hQ i hi
  have hNtr : 1 ≤ Ntr := Nat.mul_pos hK (by positivity)
  have hc0 : 1 ≤ c0 := by show 1 ≤ W0 + 2 * L + 1; omega
  have hD1 : ⌊2 * ((Ntr + 1 : ℕ) : ℝ) / θ₁⌋₊ + 4 * (Ntr + 1) + 8 ≤ D1 := by
    show _ ≤ ⌊2 * ((Ntr + 1 : ℕ) : ℝ) / θ₁⌋₊ + 4 * (Ntr + 1) + 2 * r0 + 2 * L + 8
    omega
  have hPC : ∀ y ∈ {y : Lattice | -y ∈ Q}, y + (1, 0) ∈ {y : Lattice | -y ∈ collar Q c0} ∧
      y + (0, 1) ∈ {y : Lattice | -y ∈ collar Q c0} := fun y hy =>
    ⟨⟨-y, hy, by rw [l1_neg, l1_one y _ (Or.inl rfl)]; exact_mod_cast hc0⟩,
      ⟨-y, hy, by rw [l1_neg, l1_one y _ (Or.inr rfl)]; exact_mod_cast hc0⟩⟩
  have hcand : ∀ y, y ∉ Wb → y + (1, 0) ∉ Wb ∨ y + (0, 1) ∉ Wb := by
    intro y hy
    by_contra hcon
    have hcon' := not_or.mp hcon
    have h1 : ω (-(y + (1, 0))) < -T ∨ (reachBack ω T (-(y + (1, 0)))).Finite :=
      not_not.mp hcon'.1
    have h2 : ω (-(y + (0, 1))) < -T ∨ (reachBack ω T (-(y + (0, 1)))).Finite :=
      not_not.mp hcon'.2
    rw [show -(y + (1, 0)) = -y - (1, 0) by abel] at h1
    rw [show -(y + (0, 1)) = -y - (0, 1) by abel] at h2
    exact hy (Or.inr (reachBack_finite_of_pred ω T (-y) h1 h2))
  have hchain : ¬ ∃ g : Fin (Ntr + 1) → Lattice, Function.Injective g ∧
      (∀ i, g i ∈ {y : Lattice | -y ∈ collar Q c0} ∧ g i ∈ Wb) ∧
      ∀ i : Fin (Ntr + 1), 0 < i.val → ∃ j : Fin (Ntr + 1), j.val < i.val ∧
        |(g i).1 - (g j).1| + |(g i).2 - (g j).2| ≤ (D1 : ℤ) := by
    rintro ⟨g, hinj, hmem, hch⟩
    refine (stair_trapped_components_le ω T θ₁ m1 K1 Q hθ hθ' hm hK hE).2
      ⟨fun i => -g i, neg_injective.comp hinj, fun i => ⟨(hmem i).1, (hmem i).2⟩, fun i hi => ?_⟩
    obtain ⟨j, hj, hd⟩ := hch i hi
    exact ⟨j, hj, (l1_neg (g i) (g j)).trans_le hd⟩
  have hz' : -z ∉ Wb := by
    rintro (h | h)
    · rw [neg_neg] at h
      exact absurd hzT (not_le.mpr h)
    · rw [neg_neg] at h
      exact hzB h
  obtain ⟨hnot, hdev⟩ := stair_greedy_core θ₁ q Ntr D1 Wb {y : Lattice | -y ∈ Q}
    {y : Lattice | -y ∈ collar Q c0} (-z) hθ hq1 hq2 hNtr hD1 hPC hcand hchain hz' n (fun j hj => hQ j hj.le) i hi
  exact ⟨not_lt.mp fun h => hnot (Or.inl h), fun h => hnot (Or.inr h), hdev⟩

end LPPDifferentiability
