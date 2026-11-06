/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.UniformPathDefect
public import Mathlib.Algebra.Order.Floor.Semiring

import Martin2004.Probability.WeakNegativeShape
import Differentiability.Model.Paths.RarefastLayerConcat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# No infinite oriented path of good sites

This is the final contradiction in the proof of Proposition 3.4 of the
differentiability preprint. Along an infinite oriented path of good coarse
sites, concatenate the heavy crossings and connectors. Their negative defects
contradict the almost-sure lower bound on path defects, so the event is null.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LPPDifferentiability

/-- The final contradiction in the proof of Proposition 3.4 of the differentiability
preprint. The hypotheses on `μ`, the shape
`g`, the direction `a`, and the parameters `R`, `ε`, `σ`, and the local
definitions `H`, `slope`, `rho`, `f`, `S`, `L`, `t`, `Y`, are those of the
coarse-site interface. If every environment in `G v` satisfies the good-site
witness predicate at `v` (a crossing with defect `< -ε s` in the layer of `v`,
and connectors with defect `≤ ε s / 2` to both forward neighbours), then the
event that an infinite oriented path of sites in `G` starts at `0` has
probability zero. -/
theorem measureReal_rarefast_good_oriented_path_eq_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0:ℝ), (μ (Ioi t)) ^ (1/2:ℝ)) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (R ε σ : ℝ) (_ : 0 < R) (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let slope : ℝ :=
      if σ = 1 then derivWithin H (Ioi 0) 0 else derivWithin H (Iio 0) 0
    let rho : Lattice → ℝ := fun z => (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)
    let f : Lattice → ℝ := fun z => H 0 * ((z.1 : ℝ) + (z.2 : ℝ)) + slope * rho z
    ∀ T : ℕ, 1 ≤ T → ∀ D₀ : ℝ, 1 ≤ D₀ → ∀ s : ℝ, 1 ≤ s → ∀ n : ℕ,
      let S : ℝ := 100 * (T : ℝ) * (R + 1) * (⌈s⌉₊ : ℝ)
      let L : ℕ := n + ⌈D₀ * s⌉₊
      let t : ℕ × ℕ → ℕ := fun v => v.1 + v.2
      let Y : ℕ × ℕ → ℝ := fun v => σ * ((v.1 + 2 * v.2 : ℕ) : ℝ) * S
      ∀ G : ℕ × ℕ → Set Environment,
        (∀ v, ∀ ω ∈ G v,
          (∃ c : ℝ, |c - Y v| + R * s ≤ S / 4 ∧
            ∃ u : Lattice, u.1 + u.2 = ((t v * L : ℕ) : ℤ) ∧
            ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
              (∀ i, |rho (q.vertex i) - c| ≤ R * s) ∧
              f (q.vertex (Fin.last (e.1 + e.2)) - u) - pathWeight ω q <
                -(ε * s)) ∧
          (∀ v' : ℕ × ℕ, (v' = v + (1, 0) ∨ v' = v + (0, 1)) →
            ∀ u u' : Lattice,
              u.1 + u.2 = ((t v * L + n : ℕ) : ℤ) → |rho u - Y v| ≤ S / 4 →
              u'.1 + u'.2 = (((t v + 1) * L : ℕ) : ℤ) → |rho u' - Y v'| ≤ S / 4 →
              ∃ e : ℕ × ℕ, ∃ q : Path u e,
                q.vertex (Fin.last (e.1 + e.2)) = u' ∧
                f (u' - u) - pathWeight ω q ≤ ε * s / 2 ∧
                ∀ i, |rho (q.vertex i) - Y v| ≤ 4 * S)) →
        (environmentLaw μ).real {ω | ∃ q : ℕ → ℕ × ℕ, q 0 = (0, 0) ∧
          (∀ i, q (i + 1) = q i + (1, 0) ∨ q (i + 1) = q i + (0, 1)) ∧
          ∀ i, ω ∈ G (q i)} = 0 := by
  intro H slope rho f T _hT D₀ hD₀ s hs n S L t Y G hG
  -- The almost-sure lower bound on path defects, for the unique shape.
  obtain ⟨g', ⟨hg'c, hg'h, hg'conc, hg'shape, hg'def⟩, -⟩ :=
    exists_unique_translated_shape_with_uniform_path_defect μ hneg hpos
  -- Identify that shape with `g` by uniqueness of the shape function.
  have hgg' : g = g' :=
    ExistsUnique.unique (exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos)
      (y₁ := g) (y₂ := g') ⟨hgcont, hghom, hgconc, hgshape⟩
      ⟨hg'c, hg'h, hg'conc, by
        filter_upwards [hg'shape] with ω hω
        exact hω 0⟩
  rw [← hgg'] at hg'def
  -- Numerical facts about the scale.
  have hs0 : 0 < s := by linarith
  have hεs : 0 < ε * s := mul_pos hε hs0
  have hceil : 0 < ⌈D₀ * s⌉₊ := Nat.ceil_pos.mpr (mul_pos (by linarith) hs0)
  have hL1 : 1 ≤ L := by
    show 1 ≤ n + ⌈D₀ * s⌉₊
    omega
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hnL : (n : ℝ) ≤ (L : ℝ) := by
    have hnL' : n ≤ L := Nat.le_add_right n _
    exact_mod_cast hnL'
  have hL0 : (L : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < L).ne'
  -- `f` is additive, and its value at a natural displacement.
  have hfadd : ∀ x y : Lattice, f (x + y) = f x + f y := by
    intro x y
    simp only [f, rho, Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring
  have hfe : ∀ e : ℕ × ℕ, f ((e.1 : ℤ), (e.2 : ℤ)) =
      H 0 * ((e.1 : ℝ) + (e.2 : ℝ)) + slope * ((1 - a) * (e.1 : ℝ) - a * (e.2 : ℝ)) := by
    intro e
    simp only [f, rho, Int.cast_natCast]
  -- The event is contained in the exceptional null set of the lower bound.
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
  left
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hg'def] with ω hω
  rintro ⟨q, hq0, hqstep, hqG⟩
  -- The `i`-th site of the oriented path lies in layer `i`.
  have hqt : ∀ i, t (q i) = i := by
    intro i
    induction i with
    | zero =>
        show (q 0).1 + (q 0).2 = 0
        simp [hq0]
    | succ i ih =>
        have ih' : (q i).1 + (q i).2 = i := ih
        show (q (i + 1)).1 + (q (i + 1)).2 = i + 1
        rcases hqstep i with h | h <;> rw [h] <;>
          simp only [Prod.fst_add, Prod.snd_add] <;> omega
  -- Crossing part of the witness at the site of layer `k`.
  have hcross : ∀ k : ℕ, ∃ u : Lattice,
      (u.1 + u.2 = ((k * L : ℕ) : ℤ) ∧ |rho u - Y (q k)| ≤ S / 4) ∧
      ∃ e : ℕ × ℕ, ∃ p : Path u e,
        ((u + ((e.1 : ℤ), (e.2 : ℤ))).1 + (u + ((e.1 : ℤ), (e.2 : ℤ))).2 =
            ((k * L + n : ℕ) : ℤ) ∧
          |rho (u + ((e.1 : ℤ), (e.2 : ℤ))) - Y (q k)| ≤ S / 4) ∧
        f ((e.1 : ℤ), (e.2 : ℤ)) - pathWeight ω p < -(ε * s) := by
    intro k
    obtain ⟨⟨c, hc, u, hu, e, he, p, hpc, hpd⟩, -⟩ := hG (q k) ω (hqG k)
    rw [hqt k] at hu
    have hfin := p.finish
    have h0 : |rho u - c| ≤ R * s := by
      have h0' := hpc 0
      rwa [p.start] at h0'
    have h1 : |rho (u + ((e.1 : ℤ), (e.2 : ℤ))) - c| ≤ R * s := by
      have h1' := hpc (Fin.last (e.1 + e.2))
      rwa [hfin] at h1'
    have htri : ∀ z : ℝ, |z - c| ≤ R * s → |z - Y (q k)| ≤ S / 4 := by
      intro z hz
      have htri' := abs_sub_le z c (Y (q k))
      linarith
    refine ⟨u, ⟨hu, htri _ h0⟩, e, p, ⟨?_, htri _ h1⟩, ?_⟩
    · have he' : ((e.1 : ℤ) + (e.2 : ℤ)) = (n : ℤ) := by exact_mod_cast he
      simp only [Prod.fst_add, Prod.snd_add]
      push_cast at hu ⊢
      linarith
    · rw [hfin, add_sub_cancel_left] at hpd
      exact hpd
  -- Connector part of the witness, towards the next site of the path.
  have hconn : ∀ k : ℕ, ∀ x y : Lattice,
      (x.1 + x.2 = ((k * L + n : ℕ) : ℤ) ∧ |rho x - Y (q k)| ≤ S / 4) →
      (y.1 + y.2 = (((k + 1) * L : ℕ) : ℤ) ∧ |rho y - Y (q (k + 1))| ≤ S / 4) →
      ∃ e : ℕ × ℕ, ∃ p : Path x e, x + ((e.1 : ℤ), (e.2 : ℤ)) = y ∧
        f ((e.1 : ℤ), (e.2 : ℤ)) - pathWeight ω p ≤ ε * s / 2 := by
    rintro k x y ⟨hx, hxr⟩ ⟨hy, hyr⟩
    obtain ⟨-, hcon⟩ := hG (q k) ω (hqG k)
    have hx' : x.1 + x.2 = ((t (q k) * L + n : ℕ) : ℤ) := by
      rw [hqt k]
      exact hx
    have hy' : y.1 + y.2 = (((t (q k) + 1) * L : ℕ) : ℤ) := by
      rw [hqt k]
      exact hy
    obtain ⟨e, p, hpend, hpd, -⟩ := hcon (q (k + 1)) (hqstep k) x y hx' hxr hy' hyr
    have hdisp : x + ((e.1 : ℤ), (e.2 : ℤ)) = y := by
      rw [← p.finish]
      exact hpend
    refine ⟨e, p, hdisp, ?_⟩
    have hyx : y - x = ((e.1 : ℤ), (e.2 : ℤ)) := by
      rw [← hdisp, add_sub_cancel_left]
    rw [hyx] at hpd
    exact hpd
  -- Finite concatenation along the first layers.
  obtain ⟨u₀, hPu₀, hlayers⟩ :=
    Path.exists_layer_concat_defect ω f hfadd (ε * s) (ε * s / 2)
      (fun k u => u.1 + u.2 = ((k * L : ℕ) : ℤ) ∧ |rho u - Y (q k)| ≤ S / 4)
      (fun k x => x.1 + x.2 = ((k * L + n : ℕ) : ℤ) ∧ |rho x - Y (q k)| ≤ S / 4)
      hcross hconn
  -- The lower bound with tolerance `ε s / (4 L)` from the start `u₀`.
  have hc0 : 0 < ε * s / (4 * L) := div_pos hεs (by linarith)
  obtain ⟨N, -, hN⟩ := hω u₀ (ε * s / (4 * L)) hc0
  obtain ⟨e, p, hpl, hpd⟩ := hlayers N
  have hlev : (u₀ + ((e.1 : ℤ), (e.2 : ℤ))).1 + (u₀ + ((e.1 : ℤ), (e.2 : ℤ))).2 =
      ((N * L + n : ℕ) : ℤ) := hpl.1
  have hlen : e.1 + e.2 = N * L + n := by
    have h0 : u₀.1 + u₀.2 = ((0 * L : ℕ) : ℤ) := hPu₀.1
    simp only [Prod.fst_add, Prod.snd_add] at hlev
    have hz : ((e.1 + e.2 : ℕ) : ℤ) = ((N * L + n : ℕ) : ℤ) := by
      push_cast at hlev h0 ⊢
      linarith
    exact_mod_cast hz
  have hNle : N ≤ e.1 + e.2 := by
    rw [hlen]
    calc N = N * 1 := (Nat.mul_one N).symm
      _ ≤ N * L := Nat.mul_le_mul (le_refl N) hL1
      _ ≤ N * L + n := Nat.le_add_right _ _
  obtain ⟨hminus, hplus⟩ := hN a ha₀ ha₁ e hNle p
  have hlow : f ((e.1 : ℤ), (e.2 : ℤ)) - pathWeight ω p ≥
      -(ε * s / (4 * L)) * ((e.1 + e.2 : ℕ) : ℝ) := by
    rw [hfe e]
    rcases hσ with h1 | h1
    · have hs1 : slope = derivWithin H (Ioi 0) 0 := ite_eq_left h1
      rw [hs1]
      exact hplus
    · have h1' : σ ≠ 1 := by
        rw [h1]
        norm_num
      have hs1 : slope = derivWithin H (Iio 0) 0 := ite_eq_right h1'
      rw [hs1]
      exact hminus
  -- Arithmetic: the two bounds are incompatible.
  have hX : ((e.1 + e.2 : ℕ) : ℝ) = (N : ℝ) * (L : ℝ) + (n : ℝ) := by
    rw [hlen, Nat.cast_add, Nat.cast_mul]
  have hXle : ((e.1 + e.2 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * L := by
    rw [hX]
    linarith
  have hcL : ε * s / (4 * L) * L = ε * s / 4 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hL0]
  have hcX : ε * s / (4 * L) * ((e.1 + e.2 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * (ε * s / 4) := by
    calc ε * s / (4 * L) * ((e.1 + e.2 : ℕ) : ℝ)
        ≤ ε * s / (4 * L) * (((N : ℝ) + 1) * L) :=
          mul_le_mul_of_nonneg_left hXle hc0.le
      _ = ((N : ℝ) + 1) * (ε * s / (4 * L) * L) := by ring
      _ = ((N : ℝ) + 1) * (ε * s / 4) := by rw [hcL]
  have hbelow : -(((N : ℝ) + 1) * (ε * s / 4)) ≤
      f ((e.1 : ℤ), (e.2 : ℤ)) - pathWeight ω p := by
    rw [neg_mul] at hlow
    exact le_trans (neg_le_neg hcX) hlow
  have hNn : 0 ≤ (N : ℝ) * (ε * s) := mul_nonneg (Nat.cast_nonneg N) hεs.le
  linarith

end LPPDifferentiability

end
