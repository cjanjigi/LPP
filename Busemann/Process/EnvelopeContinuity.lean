/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.EnvelopeLimits
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic

/-! All three one-sided and mixed continuity laws for signed envelope pairs. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators Topology

namespace LPP.Busemann

private theorem signed_interval_sum_tendsto
    (f : ℕ → ℤ → ℝ) (v : ℤ → ℝ)
    (hf : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (v k))) (a b : ℤ) :
    Tendsto (fun n => if a ≤ b then ∑ k ∈ Finset.Ico a b, f n k
      else -(∑ k ∈ Finset.Ico b a, f n k)) atTop
      (𝓝 (if a ≤ b then ∑ k ∈ Finset.Ico a b, v k
        else -(∑ k ∈ Finset.Ico b a, v k))) := by
  by_cases hab : a ≤ b
  · simp only [ite_eq_left hab]
    exact tendsto_finsetSum _ fun k _ => hf k
  · simp only [ite_eq_right hab]
    exact (tendsto_finsetSum _ fun k _ => hf k).neg

private theorem coordinate_path_sum_tendsto
    (u : ℕ → Lattice → Fin 2 → ℝ) (v : Lattice → Fin 2 → ℝ)
    (hu : ∀ x i, Tendsto (fun n => u n x i) atTop (𝓝 (v x i)))
    (x y : Lattice) :
    let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
      if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
      else -(∑ k ∈ Finset.Ico b a, f k)
    Tendsto (fun n =>
      S (fun k => u n (k, x.2) 0) x.1 y.1 +
        S (fun k => u n (y.1, k) 1) x.2 y.2) atTop
      (𝓝 (S (fun k => v (k, x.2) 0) x.1 y.1 +
        S (fun k => v (y.1, k) 1) x.2 y.2)) := by
  exact (signed_interval_sum_tendsto (fun n k => u n (k, x.2) 0)
    (fun k => v (k, x.2) 0) (fun k => hu (k, x.2) 0) x.1 y.1).add
      (signed_interval_sum_tendsto (fun n k => u n (y.1, k) 1)
        (fun k => v (y.1, k) 1) (fun k => hu (y.1, k) 1) x.2 y.2)

/-- Both signed envelope fields obey the lower, upper, and equal-pair continuity
laws in JR1810.03580v3 after (4.18). The mixed law assumes equality only of the
specified signed pair, and allows arbitrary changes of approach side. -/
theorem signed_envelopes_tendsto
    (g : Quadrant → ℝ) (D : ℕ → SupportTilt g)
    (happrox : ∀ h : SupportTilt g, ∃ a b : ℕ → ℕ,
      StrictMono (fun n => (D (a n)).1.1) ∧
      StrictAnti (fun n => (D (b n)).1.1) ∧
      (∀ n, (D (a n)).1.1 < h.1.1 ∧ h.1.1 < (D (b n)).1.1) ∧
      Tendsto (fun n => (D (a n)).1) atTop (𝓝 h.1) ∧
      Tendsto (fun n => (D (b n)).1) atTop (𝓝 h.1)) :
    let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ :=
      fun j x i s => s.2 j x i
    let Q : Set ProcessSample := {s | ∀ j k x,
      (D j).1.1 ≤ (D k).1.1 →
        X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
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
    let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
      if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
      else -(∑ k ∈ Finset.Ico b a, f k)
    let Rminus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
      fun h x y s =>
        S (fun k => eMinus h (k, x.2) 0 s) x.1 y.1 +
          S (fun k => eMinus h (y.1, k) 1 s) x.2 y.2
    let Rplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
      fun h x y s =>
        S (fun k => ePlus h (k, x.2) 0 s) x.1 y.1 +
          S (fun k => ePlus h (y.1, k) 1 s) x.2 y.2
    (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ x y : Lattice,
      ∀ hs : ℕ → SupportTilt g,
        (∀ n, (hs n).1.1 < h.1.1) → Tendsto hs atTop (𝓝 h) →
          Tendsto (fun n => Rminus (hs n) x y s) atTop (𝓝 (Rminus h x y s)) ∧
          Tendsto (fun n => Rplus (hs n) x y s) atTop (𝓝 (Rminus h x y s))) ∧
    (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ x y : Lattice,
      ∀ hs : ℕ → SupportTilt g,
        (∀ n, h.1.1 < (hs n).1.1) → Tendsto hs atTop (𝓝 h) →
          Tendsto (fun n => Rminus (hs n) x y s) atTop (𝓝 (Rplus h x y s)) ∧
          Tendsto (fun n => Rplus (hs n) x y s) atTop (𝓝 (Rplus h x y s))) ∧
    (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ x y : Lattice,
      Rminus h x y s = Rplus h x y s →
      ∀ hs : ℕ → SupportTilt g, Tendsto hs atTop (𝓝 h) →
        Tendsto (fun n => Rminus (hs n) x y s) atTop (𝓝 (Rminus h x y s)) ∧
        Tendsto (fun n => Rplus (hs n) x y s) atTop (𝓝 (Rminus h x y s))) := by
  classical
  let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ :=
    fun j x i s => s.2 j x i
  let Q : Set ProcessSample := {s | ∀ j k x,
    (D j).1.1 ≤ (D k).1.1 →
      X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
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
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
    else -(∑ k ∈ Finset.Ico b a, f k)
  let Rminus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
    fun h x y s =>
      S (fun k => eMinus h (k, x.2) 0 s) x.1 y.1 +
        S (fun k => eMinus h (y.1, k) 1 s) x.2 y.2
  let Rplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
    fun h x y s =>
      S (fun k => ePlus h (k, x.2) 0 s) x.1 y.1 +
        S (fun k => ePlus h (y.1, k) 1 s) x.2 y.2
  change
    (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ x y : Lattice,
      ∀ hs : ℕ → SupportTilt g,
        (∀ n, (hs n).1.1 < h.1.1) → Tendsto hs atTop (𝓝 h) →
          Tendsto (fun n => Rminus (hs n) x y s) atTop (𝓝 (Rminus h x y s)) ∧
          Tendsto (fun n => Rplus (hs n) x y s) atTop (𝓝 (Rminus h x y s))) ∧
    (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ x y : Lattice,
      ∀ hs : ℕ → SupportTilt g,
        (∀ n, h.1.1 < (hs n).1.1) → Tendsto hs atTop (𝓝 h) →
          Tendsto (fun n => Rminus (hs n) x y s) atTop (𝓝 (Rplus h x y s)) ∧
          Tendsto (fun n => Rplus (hs n) x y s) atTop (𝓝 (Rplus h x y s))) ∧
    (∀ s ∈ Q, ∀ h : SupportTilt g, ∀ x y : Lattice,
      Rminus h x y s = Rplus h x y s →
      ∀ hs : ℕ → SupportTilt g, Tendsto hs atTop (𝓝 h) →
        Tendsto (fun n => Rminus (hs n) x y s) atTop (𝓝 (Rminus h x y s)) ∧
        Tendsto (fun n => Rplus (hs n) x y s) atTop (𝓝 (Rminus h x y s)))
  obtain ⟨hUnitLower, hUnitUpper⟩ := unit_envelopes_tendsto_of_one_sided g D happrox
  have hLower : ∀ s ∈ Q, ∀ h : SupportTilt g, ∀ x y : Lattice,
      ∀ hs : ℕ → SupportTilt g,
        (∀ n, (hs n).1.1 < h.1.1) → Tendsto hs atTop (𝓝 h) →
          Tendsto (fun n => Rminus (hs n) x y s) atTop (𝓝 (Rminus h x y s)) ∧
          Tendsto (fun n => Rplus (hs n) x y s) atTop (𝓝 (Rminus h x y s)) := by
    intro s hs h x y v hv hlim
    have hu := hUnitLower s hs h v hv hlim
    exact ⟨coordinate_path_sum_tendsto (fun n z i => eMinus (v n) z i s)
      (fun z i => eMinus h z i s) (fun z i => (hu z i).1) x y,
      coordinate_path_sum_tendsto (fun n z i => ePlus (v n) z i s)
        (fun z i => eMinus h z i s) (fun z i => (hu z i).2) x y⟩
  have hUpper : ∀ s ∈ Q, ∀ h : SupportTilt g, ∀ x y : Lattice,
      ∀ hs : ℕ → SupportTilt g,
        (∀ n, h.1.1 < (hs n).1.1) → Tendsto hs atTop (𝓝 h) →
          Tendsto (fun n => Rminus (hs n) x y s) atTop (𝓝 (Rplus h x y s)) ∧
          Tendsto (fun n => Rplus (hs n) x y s) atTop (𝓝 (Rplus h x y s)) := by
    intro s hs h x y v hv hlim
    have hu := hUnitUpper s hs h v hv hlim
    exact ⟨coordinate_path_sum_tendsto (fun n z i => eMinus (v n) z i s)
      (fun z i => ePlus h z i s) (fun z i => (hu z i).1) x y,
      coordinate_path_sum_tendsto (fun n z i => ePlus (v n) z i s)
        (fun z i => ePlus h z i s) (fun z i => (hu z i).2) x y⟩
  refine ⟨hLower, hUpper, ?_⟩
  intro s hs h x y hpair v hlim
  -- Equal first coordinates give the same literal guards, even for distinct tilts.
  have hSame (w : SupportTilt g) (hw : w.1.1 = h.1.1) :
      Rminus w x y s = Rminus h x y s ∧ Rplus w x y s = Rplus h x y s := by
    constructor
    · simp only [Rminus, S, eMinus, Eminus, hw]
    · simp only [Rplus, S, ePlus, Eplus, hw]
  obtain ⟨a, b, _, _, hab, hla, hlb⟩ := happrox h
  have ha : Tendsto (fun n => D (a n)) atTop (𝓝 h) := tendsto_subtype_rng.mpr hla
  have hb : Tendsto (fun n => D (b n)) atTop (𝓝 h) := tendsto_subtype_rng.mpr hlb
  -- These two sequences are local to h and v; neither is a global parameter map.
  let lo : ℕ → SupportTilt g := fun n =>
    if (v n).1.1 < h.1.1 then v n else D (a n)
  let hi : ℕ → SupportTilt g := fun n =>
    if h.1.1 < (v n).1.1 then v n else D (b n)
  have hloSide (n : ℕ) : (lo n).1.1 < h.1.1 := by
    dsimp only [lo]
    split_ifs with hn
    · exact hn
    · exact (hab n).1
  have hhiSide (n : ℕ) : h.1.1 < (hi n).1.1 := by
    dsimp only [hi]
    split_ifs with hn
    · exact hn
    · exact (hab n).2
  have hloLim : Tendsto lo atTop (𝓝 h) := hlim.if' ha
  have hhiLim : Tendsto hi atTop (𝓝 h) := hlim.if' hb
  have hLow := hLower s hs h x y lo hloSide hloLim
  have hHigh := hUpper s hs h x y hi hhiSide hhiLim
  rw [← hpair] at hHigh
  -- Neighborhood membership joins all three cases without inferring edge equality.
  have hmerge (f : SupportTilt g → ℝ)
      (hflo : Tendsto (fun n => f (lo n)) atTop (𝓝 (Rminus h x y s)))
      (hfhi : Tendsto (fun n => f (hi n)) atTop (𝓝 (Rminus h x y s)))
      (hfixed : ∀ w : SupportTilt g, w.1.1 = h.1.1 → f w = Rminus h x y s) :
      Tendsto (fun n => f (v n)) atTop (𝓝 (Rminus h x y s)) := by
    rw [tendsto_def] at hflo hfhi ⊢
    intro U hU
    filter_upwards [hflo U hU, hfhi U hU] with n hnlo hnhi
    change f (lo n) ∈ U at hnlo
    change f (hi n) ∈ U at hnhi
    change f (v n) ∈ U
    by_cases hn : (v n).1.1 < h.1.1
    · simpa only [lo, ite_eq_left hn] using hnlo
    · by_cases hp : h.1.1 < (v n).1.1
      · simpa only [hi, ite_eq_left hp] using hnhi
      · have heq : (v n).1.1 = h.1.1 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
        rw [hfixed (v n) heq]
        exact mem_of_mem_nhds hU
  exact ⟨hmerge (fun w => Rminus w x y s) hLow.1 hHigh.1
    (fun w hw => (hSame w hw).1),
    hmerge (fun w => Rplus w x y s) hLow.2 hHigh.2
      (fun w hw => (hSame w hw).2.trans hpair.symm)⟩

end LPP.Busemann
