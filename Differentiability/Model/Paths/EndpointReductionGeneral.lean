/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.DefectAlgebra
public import Differentiability.Model.StairTrim
public import Differentiability.Model.Paths.GridEntranceExitPoints
public import Differentiability.Model.Paths.GreedyAttachmentSequence
public import LPP_Foundations.Model.Paths.Split
public import LPP_Foundations.Model.Paths.Level
public import Differentiability.Analysis.GridScaleCounts
import Mathlib.Tactic

/-! # Trimming and endpoint reduction for general weights

This file follows the proof of Proposition 5.9 of the differentiability preprint, the remark on
bounded and unbounded weights in Section 5, and items (C2) and (C8) in Section B.3. A
witness path is trimmed by at most `r₀` steps at each end (`stair_trim`); a path with at most
`2 r₀ + 1` steps cannot be the witness; trimming costs at most `ε s_k / 64`; entrance and exit
chains along the greedy staircases through the trimmed ends are glued on; the total defect is
below `-ε s_k / 2`.
-/

public section

namespace LPPDifferentiability

/-- On a path whose vertices lie in `Q`, where the weights are at most `t`, the defect for a slope
of absolute value at most `K` is at least `-n (|G₀| + K + t)`, `n` the number of steps. -/
private theorem support_defect_lower_bound (ω : Environment) (a G0 sl K t : ℝ) (Q : Set Lattice)
    (ha0 : 0 < a) (ha1 : a < 1) (hsl : |sl| ≤ K) (hω : ∀ z ∈ Q, ω z ≤ t)
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (hp : ∀ i, p.vertex i ∈ Q) :
    -(((d.1 : ℝ) + (d.2 : ℝ)) * (|G0| + K + t)) ≤ Path.supportDefect a G0 sl ω p := by
  have hw : pathWeight ω p ≤ ((d.1 : ℝ) + (d.2 : ℝ)) * t := by
    unfold pathWeight
    calc ∑ i : Fin (d.1 + d.2), ω (p.vertex i.castSucc)
        ≤ ∑ _i : Fin (d.1 + d.2), t := Finset.sum_le_sum fun i _ => hω _ (hp _)
      _ = ((d.1 : ℝ) + (d.2 : ℝ)) * t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add]
  have hd1 : (0 : ℝ) ≤ d.1 := Nat.cast_nonneg _
  have hd2 : (0 : ℝ) ≤ d.2 := Nat.cast_nonneg _
  have hK : 0 ≤ K := (abs_nonneg sl).trans hsl
  have hm1 := mul_nonneg ha0.le (add_nonneg hd1 hd2)
  have hm2 := mul_nonneg (sub_nonneg.2 ha1.le) (add_nonneg hd1 hd2)
  have htr : |(1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)| ≤ (d.1 : ℝ) + (d.2 : ℝ) := by
    rw [abs_le]; constructor <;> nlinarith
  have hsr : -(K * ((d.1 : ℝ) + (d.2 : ℝ))) ≤
      sl * ((1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)) := by
    have h1 : |sl * ((1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ))| ≤ K * ((d.1 : ℝ) + (d.2 : ℝ)) := by
      rw [abs_mul]; exact mul_le_mul hsl htr (abs_nonneg _) hK
    linarith [neg_abs_le (sl * ((1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)))]
  have hg : -(|G0| * ((d.1 : ℝ) + (d.2 : ℝ))) ≤ G0 * ((d.1 : ℝ) + (d.2 : ℝ)) := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le G0) (add_nonneg hd1 hd2)
    linarith
  simp only [Path.supportDefect, supportingFunctional, transverseCoordinate]
  linarith

/-- Every vertex of a prefix is a vertex of the path. -/
private theorem prefix_vertex {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1)) (i : Fin ((p.splitDisplacement k).1 + (p.splitDisplacement k).2 + 1)) :
    ∃ j, (p.prefixPath k).vertex i = p.vertex j := ⟨_, rfl⟩

/-- Every vertex of a suffix is a vertex of the path. -/
private theorem suffix_vertex {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (k : Fin (d.1 + d.2 + 1))
    (i : Fin ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2 + 1)) :
    ∃ j, (p.suffix k).vertex i = p.vertex j := ⟨_, rfl⟩

/-- Splitting a path at two vertices `i₀ ≤ i₁` gives a prefix, a middle part and a suffix whose
defects add up, with the prefix and the suffix of the stated numbers of steps. -/
private theorem split_three (ω : Environment) (a G0 sl : ℝ) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (i0 i1 : Fin (d.1 + d.2 + 1)) (h : i0.val ≤ i1.val) :
    ∃ w : Lattice, w = p.vertex i1 ∧ ∃ (dP dM dT : ℕ × ℕ) (P : Path u dP)
      (M : Path (p.vertex i0) dM) (T : Path w dT),
      Path.supportDefect a G0 sl ω p =
        Path.supportDefect a G0 sl ω P + Path.supportDefect a G0 sl ω M +
          Path.supportDefect a G0 sl ω T ∧
      p.vertex i0 + ((dM.1 : ℤ), (dM.2 : ℤ)) = w ∧
      dP.1 + dP.2 = i0.val ∧ dT.1 + dT.2 = d.1 + d.2 - i1.val ∧
      (∀ i, ∃ j, P.vertex i = p.vertex j) ∧ (∀ i, ∃ j, M.vertex i = p.vertex j) ∧
      (∀ i, ∃ j, T.vertex i = p.vertex j) := by
  have hsd := p.splitDisplacement_length i0
  have hsl := p.suffix_length i0
  have hj : i1.val - i0.val <
      (d - p.splitDisplacement i0).1 + (d - p.splitDisplacement i0).2 + 1 := by
    have := i1.isLt; omega
  let jj : Fin ((d - p.splitDisplacement i0).1 + (d - p.splitDisplacement i0).2 + 1) :=
    ⟨i1.val - i0.val, hj⟩
  have hjj : jj.val = i1.val - i0.val := rfl
  have hv : (p.suffix i0).vertex jj = p.vertex i1 := by
    show p.vertex _ = p.vertex i1
    congr 1
    apply Fin.ext
    show i0.val + (i1.val - i0.val) = i1.val
    omega
  have hmid := (p.suffix i0).split_vertex jj
  have hT := (p.suffix i0).suffix_length jj
  refine ⟨(p.suffix i0).vertex jj, hv, _, _, _, p.prefixPath i0, (p.suffix i0).prefixPath jj,
    (p.suffix i0).suffix jj, ?_, hmid.symm, hsd, ?_, fun i => prefix_vertex p i0 i, ?_, ?_⟩
  · rw [Path.path_support_defect_split a G0 sl ω p i0,
      Path.path_support_defect_split a G0 sl ω (p.suffix i0) jj]
    ring
  · have := i1.isLt
    omega
  · intro i
    obtain ⟨j, hj⟩ := prefix_vertex (p.suffix i0) jj i
    obtain ⟨j', hj'⟩ := suffix_vertex p i0 j
    exact ⟨j', hj.trans hj'⟩
  · intro i
    obtain ⟨j, hj⟩ := suffix_vertex (p.suffix i0) jj i
    obtain ⟨j', hj'⟩ := suffix_vertex p i0 j
    exact ⟨j', hj.trans hj'⟩

/-- **Trimming and endpoint reduction for general weights** (Proposition 5.9, items (C2) and
(C8) of Section B.3). In an environment on which the geometry event holds in a collar of `Q` and the
weights in `Q` are at most `t_k`, a path in the region with a defect below `-ε s_k` for one slope
gives a crossing between two coarse levels with defect below `-ε s_k / 2` in the strip of
half-width `(R + 2 c₁) s_k`. -/
theorem endpoint_pair_of_mem_general (ω : Environment) (a G0 dl dr K c1 A R ε T : ℝ) (M k J m1 K1 : ℕ)
    (Q : Set Lattice) :
  let θ₁ : ℝ := min a (1 - a) / 5
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
  let gf : Lattice → ℕ → Lattice := fun u t =>
    GreedyAttachment.vertex u a {y | (reach ω T y).Finite} t
  let gb : Lattice → ℕ → Lattice := fun u t =>
    -GreedyAttachment.vertex (-u) a {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite} t
  0 < a → a < 1 → 1 ≤ m1 → 1 ≤ K1 → 1 ≤ c1 → 0 < ε → 1 ≤ J →
  J ≤ ⌈((M : ℝ) - 1) / 4⌉₊ → ⌈((M : ℝ) - 1) / 4⌉₊ ≤ k → 0 < k →
  16 * c1 * ∑' i : ℕ, ((i + J : ℕ) : ℝ) ^ 2 / 2 ^ (i + J) ≤ ε / 8 →
  |dl| ≤ K → |dr| ≤ K →
  2 * (r0 : ℝ) * (ε / 512 * 2 ^ k / (k : ℝ) + |G0| + K) ≤ ε * 2 ^ k / 64 →
  (∀ z : Lattice, |((z.1 + z.2 : ℤ) : ℝ)| ≤ A * 2 ^ M →
    |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ R * 2 ^ k → z ∈ Q) →
  Egeo ω T Q → (∀ z ∈ Q, ω z ≤ ε / 512 * 2 ^ k / (k : ℝ)) →
  (∀ u : Lattice, |((u.1 + u.2 : ℤ) : ℝ)| ≤ A * 2 ^ M →
    |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)| ≤ R * 2 ^ k →
    ∀ j : ℕ, J ≤ j → j ≤ ⌈((M : ℝ) - 1) / 4⌉₊ →
    ∀ I : ℤ, ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ M →
    ((-T ≤ ω u ∧ ¬ (reachBack ω T u).Finite) →
      (⌊((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌋ - 1) *
        ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ≤ I →
      I + ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) ≤ u.1 + u.2 →
      ∀ z₀ z₁ : Lattice, z₀ = gb u (u.1 + u.2 - I).toNat →
        z₁ = gb u (u.1 + u.2 - (I + ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ))).toNat →
      ∃ (D : ℕ × ℕ) (y : Path z₀ D),
        z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
        Path.supportDefect a G0 dl ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        Path.supportDefect a G0 dr ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
            ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))) ∧
    (¬ (reach ω T u).Finite →
      u.1 + u.2 ≤ I →
      I + ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) ≤
        (⌈((u.1 + u.2 : ℤ) : ℝ) / ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) *
          ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) →
      ∀ z₀ z₁ : Lattice, z₀ = gf u (I - (u.1 + u.2)).toNat →
        z₁ = gf u (I + ((2 ^ (M - 4 * j - 1) : ℕ) : ℤ) - (u.1 + u.2)).toNat →
      ∃ (D : ℕ × ℕ) (y : Path z₀ D),
        z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
        Path.supportDefect a G0 dl ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        Path.supportDefect a G0 dr ω y ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε / 512 * 2 ^ k / (k : ℝ)) ∧
        ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) -
            ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤
          c1 * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)))) →
  (∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
    (∀ i, |((q.vertex i).1 : ℝ) + ((q.vertex i).2 : ℝ)| ≤ A * 2 ^ M ∧
      |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ R * 2 ^ k) ∧
    Path.minimumSupportDefect a G0 dl dr ω q < -(ε * 2 ^ k)) →
  ∃ p : ℤ × ℤ, (((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ∣ p.1 ∧ |(p.1 : ℝ)| ≤ (A + 4) * 2 ^ M) ∧
    (((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ∣ p.2 ∧ |(p.2 : ℝ)| ≤ (A + 4) * 2 ^ M) ∧
    2 * ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) ≤ p.2 - p.1 ∧
    ∃ sl : ℝ, (sl = dr ∨ sl = dl) ∧
    ∃ u : Lattice, u.1 + u.2 = p.1 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = (p.2 - p.1).toNat ∧
    ∃ q : Path u e,
      (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
        (R + 2 * c1) * 2 ^ k) ∧
      Path.supportDefect a G0 sl ω q < -(ε / 2 * 2 ^ k) := by
  intro θ₁ reach reachBack Ntr _W0 L r0 _D1 _d0 _c0 _collar _Egeo gf gb ha0 ha1 hm1 hK1 hc1 hε hJ1
    hJ hjk hk hJε hdl hdr hscal hQ hE hω hgrid hev
  have hr0 : r0 = K1 * (2 * L + 1) + Ntr := rfl
  have hr0pos : 1 ≤ r0 := by
    have : 1 ≤ K1 * (2 * L + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  obtain ⟨u, e, x, hreg, hmin⟩ := hev
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs0 : (0 : ℝ) < 2 ^ k := by positivity
  have hεs : 0 < ε * 2 ^ k := mul_pos hε hs0
  have ht0 : 0 < ε / 512 * 2 ^ k / (k : ℝ) := div_pos (mul_pos (div_pos hε (by norm_num)) hs0) hkR
  have hc1' : 0 ≤ c1 := by linarith
  have hxQ : ∀ i, x.vertex i ∈ Q := fun i => by
    have h := hreg i
    refine hQ _ ?_ h.2
    have h1 := h.1
    push_cast
    exact h1
  have hul : ∀ i, |(((x.vertex i).1 + (x.vertex i).2 : ℤ) : ℝ)| ≤ A * 2 ^ M := fun i => by
    have h1 := (hreg i).1
    push_cast
    exact h1
  obtain ⟨sl, hsl, hxd⟩ :
      ∃ sl : ℝ, (sl = dr ∨ sl = dl) ∧ Path.supportDefect a G0 sl ω x < -(ε * 2 ^ k) := by
    rcases min_lt_iff.1 hmin with h | h
    · exact ⟨dl, Or.inr rfl, h⟩
    · exact ⟨dr, Or.inl rfl, h⟩
  have hKs : |sl| ≤ K := by rcases hsl with h | h <;> rw [h] <;> assumption
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = |G0| + K + ε / 512 * 2 ^ k / (k : ℝ) := ⟨_, rfl⟩
  have hBd0 : 0 ≤ Bd := by
    have h1 := abs_nonneg G0
    have h2 : 0 ≤ K := (abs_nonneg sl).trans hKs
    rw [hBd]; linarith
  have hscal' : 2 * (r0 : ℝ) * Bd ≤ ε * 2 ^ k / 64 := by rw [hBd]; linarith
  have hlowQ : ∀ {u' : Lattice} {d' : ℕ × ℕ} (q : Path u' d'),
      (∀ i, ∃ j, q.vertex i = x.vertex j) →
      -(((d'.1 : ℝ) + (d'.2 : ℝ)) * Bd) ≤ Path.supportDefect a G0 sl ω q := fun q hq => by
    rw [hBd]
    exact support_defect_lower_bound ω a G0 sl K _ Q ha0 ha1 hKs hω q (fun i => by
      obtain ⟨j, hj⟩ := hq i
      rw [hj]
      exact hxQ j)
  have hlow := hlowQ x (fun i => ⟨i, rfl⟩)
  have hn : 2 * r0 + 2 ≤ e.1 + e.2 := by
    by_contra hlt
    have hn1 : ((e.1 : ℝ) + (e.2 : ℝ)) ≤ 2 * (r0 : ℝ) + 1 := by
      have : e.1 + e.2 ≤ 2 * r0 + 1 := by omega
      exact_mod_cast this
    have hr1 : (1 : ℝ) ≤ r0 := by exact_mod_cast hr0pos
    have h1 := mul_le_mul_of_nonneg_right hn1 hBd0
    have h2 := mul_nonneg (sub_nonneg.2 hr1) hBd0
    linarith
  -- Trimming.
  have hθ : 0 < θ₁ := div_pos (lt_min ha0 (sub_pos.2 ha1)) (by norm_num)
  have hθ' : θ₁ ≤ 1 / 10 := by
    have h1 := min_le_left a (1 - a)
    have h2 := min_le_right a (1 - a)
    show min a (1 - a) / 5 ≤ 1 / 10
    linarith
  have htrim : ∀ s : ℕ, s + r0 ≤ e.1 + e.2 →
      (∀ i : Fin (e.1 + e.2 + 1), s ≤ i.val → i.val ≤ s + r0 → x.vertex i ∈ Q) →
      (∃ i : Fin (e.1 + e.2 + 1), s ≤ i.val ∧ i.val ≤ s + r0 ∧
        ¬ (reach ω T (x.vertex i)).Finite) ∧
      (∃ i : Fin (e.1 + e.2 + 1), s ≤ i.val ∧ i.val ≤ s + r0 ∧
        -T ≤ ω (x.vertex i) ∧ ¬ (reachBack ω T (x.vertex i)).Finite) :=
    fun s hs hQs =>
      ⟨(stair_trim ω T θ₁ m1 K1 Q hθ hθ' hm1 hK1 hE u e x s hs hQs).2.1,
       (stair_trim ω T θ₁ m1 K1 Q hθ hθ' hm1 hK1 hE u e x s hs hQs).2.2⟩
  obtain ⟨-, i0, hi0a, hi0b, hωu, hnb⟩ := htrim 0 (by omega) (fun i _ _ => hxQ i)
  obtain ⟨⟨i1, hi1a, hi1b, hnr⟩, -⟩ :=
    htrim (e.1 + e.2 - r0) (by omega) (fun i _ _ => hxQ i)
  have hi01 : i0.val ≤ i1.val := by omega
  obtain ⟨w, hw, dP, dM, dT, xP, xM, xT, hsplit, hmid, hdP, hdT, hPv, hMv, hTv⟩ :=
    split_three ω a G0 sl x i0 i1 hi01
  subst hw
  have hnP : ((dP.1 : ℝ) + (dP.2 : ℝ)) ≤ r0 := by
    have : dP.1 + dP.2 ≤ r0 := by omega
    exact_mod_cast this
  have hnT : ((dT.1 : ℝ) + (dT.2 : ℝ)) ≤ r0 := by
    have : dT.1 + dT.2 ≤ r0 := by omega
    exact_mod_cast this
  have hMd : Path.supportDefect a G0 sl ω xM < -(ε * 2 ^ k) + ε * 2 ^ k / 64 := by
    have h1 := mul_le_mul_of_nonneg_right hnP hBd0
    have h2 := mul_le_mul_of_nonneg_right hnT hBd0
    have hP := hlowQ xP hPv
    have hT := hlowQ xT hTv
    linarith
  have hPb : ∀ v : Lattice, gb v (v.1 + v.2 - (v.1 + v.2)).toNat = v := fun v => by simp [gb]
  have hPf : ∀ v : Lattice, gf v ((v.1 + v.2) - (v.1 + v.2)).toNat = v := fun v => by simp [gf]
  have hlevb : ∀ (v : Lattice) (I : ℤ), I ≤ v.1 + v.2 →
      (gb v (v.1 + v.2 - I).toNat).1 + (gb v (v.1 + v.2 - I).toNat).2 = I := by
    intro v I hI
    have h := GreedyAttachment.level (-v) a {y | ω (-y) < -T ∨ (reachBack ω T (-y)).Finite}
      (v.1 + v.2 - I).toNat
    have ht : (((v.1 + v.2 - I).toNat : ℕ) : ℤ) = v.1 + v.2 - I :=
      Int.toNat_of_nonneg (by omega)
    simp only [gb, Prod.fst_neg, Prod.snd_neg] at h ⊢
    omega
  have hlevf : ∀ (v : Lattice) (I : ℤ), v.1 + v.2 ≤ I →
      (gf v (I - (v.1 + v.2)).toNat).1 + (gf v (I - (v.1 + v.2)).toNat).2 = I := by
    intro v I hI
    have h := GreedyAttachment.level v a {y | (reach ω T y).Finite} (I - (v.1 + v.2)).toNat
    have ht : (((I - (v.1 + v.2)).toNat : ℕ) : ℤ) = I - (v.1 + v.2) :=
      Int.toNat_of_nonneg (by omega)
    simp only [gf]
    omega
  have hg0 := hgrid (x.vertex i0) (hul i0) (hreg i0).2
  have hg1 := hgrid (x.vertex i1) (hul i1) (hreg i1).2
  -- The entrance path of the trimmed start and the exit path of the trimmed end.
  obtain ⟨z, D1, y1, -, hzl, hD1, a1, b1, c1b⟩ :=
    grid_entrance_chain_of_points ω a G0 dl dr c1 A ε M k J
      (fun I => gb (x.vertex i0) ((x.vertex i0).1 + (x.vertex i0).2 - I).toNat) (x.vertex i0)
      hc1' hε hJ1 hJ hjk hk hJε (hul i0) (hPb _) (fun I hI => hlevb _ I hI)
      (fun j h1 h2 I hd hI hlo hhi => (hg0 j h1 h2 I hd hI).1 ⟨hωu, hnb⟩ hlo hhi)
  obtain ⟨z2, D2, y2, -, hz2l, hD2, a2, b2, c2b⟩ :=
    grid_exit_chain_of_points ω a G0 dl dr c1 A ε M k J
      (fun I => gf (x.vertex i1) (I - ((x.vertex i1).1 + (x.vertex i1).2)).toNat) (x.vertex i1)
      hc1' hε hJ1 hJ hjk hk hJε (hul i1) (hPf _) (fun I hI => hlevf _ I hI)
      (fun j h1 h2 I hd hI hlo hhi => (hg1 j h1 h2 I hd hI).2 hnr hlo hhi)
  have hy1 : G0 * ((D1.1 : ℝ) + (D1.2 : ℝ)) + sl * ((1 - a) * (D1.1 : ℝ) - a * (D1.2 : ℝ)) -
      pathWeight ω y1 ≤ ε * 2 ^ k / 8 + ε * 2 ^ k / 16 := by
    rcases hsl with h | h <;> rw [h] <;> assumption
  have hy2 : G0 * ((D2.1 : ℝ) + (D2.2 : ℝ)) + sl * ((1 - a) * (D2.1 : ℝ) - a * (D2.2 : ℝ)) -
      pathWeight ω y2 ≤ ε * 2 ^ k / 8 + ε * 2 ^ k / 16 := by
    rcases hsl with h | h <;> rw [h] <;> assumption
  obtain ⟨E1, x1, hE1, hd1, -, hv1⟩ := exists_concat_defect_eq ω a G0 sl sl xM hmid y2
  obtain ⟨E2, x2, hE2, hd2, -, hv2⟩ := exists_concat_defect_eq ω a G0 sl sl y1 hD1 x1
  have hl0 : 0 < 2 ^ (M - 4 * J - 1) := by positivity
  have hlm := grid_mesh_le M J
  obtain ⟨hdv1, -, -, -, hb1, -⟩ := grid_level_endpoints (A := A) hl0 hlm (hul i0)
  obtain ⟨-, hdv2, -, -, -, hb2⟩ := grid_level_endpoints (A := A) hl0 hlm (hul i1)
  have hle : (x.vertex i0).1 + (x.vertex i0).2 ≤ (x.vertex i1).1 + (x.vertex i1).2 := by
    have h0 := x.level i0
    have h1 := x.level i1
    have : (i0.val : ℤ) ≤ i1.val := by exact_mod_cast hi01
    omega
  have hgap := grid_level_endpoints_gap hl0 hle
  generalize (⌊(((x.vertex i0).1 + (x.vertex i0).2 : ℤ) : ℝ) /
    ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌋ - 1) * ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) = Im
    at hzl hdv1 hb1 hgap
  generalize (⌈(((x.vertex i1).1 + (x.vertex i1).2 : ℤ) : ℝ) /
    ((2 ^ (M - 4 * J - 1) : ℕ) : ℝ)⌉ + 1) * ((2 ^ (M - 4 * J - 1) : ℕ) : ℤ) = Ip
    at hz2l hdv2 hb2 hgap
  have hzz : z + ((E2.1 : ℤ), (E2.2 : ℤ)) = z2 := hE2.trans (hE1.trans hD2)
  have hzf := congrArg Prod.fst hzz
  have hzs := congrArg Prod.snd hzz
  simp only [Prod.fst_add, Prod.snd_add] at hzf hzs
  have hlen : E2.1 + E2.2 = (Ip - Im).toNat := by omega
  have hvert : ∀ i, |(1 - a) * ((x2.vertex i).1 : ℝ) - a * ((x2.vertex i).2 : ℝ)| ≤
      (R + 2 * c1) * 2 ^ k := by
    intro i
    have e2 : (R + 2 * c1) * 2 ^ k = R * 2 ^ k + 2 * c1 * 2 ^ k := by ring
    rw [e2]
    rcases hv2 i with ⟨j, hj⟩ | ⟨j, hj⟩ <;> rw [hj]
    · have h1 := abs_le.1 (c1b j)
      have h2 := abs_le.1 (hreg i0).2
      rw [abs_le]; constructor <;> linarith
    · rcases hv1 j with ⟨j', hj'⟩ | ⟨j', hj'⟩ <;> rw [hj']
      · obtain ⟨j'', hj''⟩ := hMv j'
        rw [hj'']
        have h1 := abs_le.1 (hreg j'').2
        have h3 : 0 ≤ 2 * c1 * 2 ^ k := mul_nonneg (by linarith) hs0.le
        rw [abs_le]; constructor <;> linarith
      · have h1 := abs_le.1 (c2b j')
        have h2 := abs_le.1 (hreg i1).2
        rw [abs_le]; constructor <;> linarith
  refine ⟨(Im, Ip), ⟨hdv1, hb1⟩, ⟨hdv2, hb2⟩, hgap, sl, hsl, z, hzl, E2, hlen, x2, hvert, ?_⟩
  simp only [Path.supportDefect, supportingFunctional, transverseCoordinate] at hMd ⊢
  linarith

end LPPDifferentiability
