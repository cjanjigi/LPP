/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.ERealFloorRate
public import Martin2004.Probability.FloorPhaseSandwich
public import ProbabilityBasics.Probability.LiggettConvergence
public import LPP_Foundations.Probability.PassageIntegrable
public import LPP_Foundations.Probability.PassageMeanMonotone
public import Martin2004.Probability.RandomPhaseMeasure
import Mathlib.Tactic

/-!
# Random phase: the Liggett limit on the phase space

Martin (2004), Proposition 2.1 is stated for every real direction `x`. Martin only cites a
superadditive Kingman theorem and gives no argument when the fractional parts of `n x` keep
changing. Here a uniform phase `θ` in the unit square is added, and the array
`X_{m,n}(θ, ω)` is the passage time from `⌊m x + θ⌋` to `⌊n x + θ⌋`.

This file checks the hypotheses of Liggett's convergence theorem `exists_liggett_convergence`
for the negative of this array, on the product of the phase law and the environment law:

* each entry is measurable (one helper handles the floor-dependent endpoints);
* `X_{0,n}` is integrable;
* `X_{l,m} + X_{m,n} ≤ X_{l,n}` (superadditivity, (2.2) of Martin (2004)), for every phase;
* `X_{m,n} ∘ Φ = X_{m+1,n+1}` for the skew map `Φ` of `RandomPhaseMeasure`, which preserves the
  law, so the shifted sequences are identically distributed;
* `∫ X_{0,n} ≤ c n`, from the linear bound for the expected floor rate.

The public output is one theorem with explicit terms and no new public definition. The array,
the skew map and the phase law are private to this file.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace LPPDifferentiability

/-- The random-phase law: the uniform law on the unit square times the environment law. -/
private noncomputable abbrev phaseLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measure ((ℝ × ℝ) × Environment) :=
  ((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))).prod
    (environmentLaw μ)

/-- The skew map: add the direction to the phase modulo one, and shift the
environment by the integer part. Same map as in `measurePreserving_phase_skew`. -/
private noncomputable def phaseSkew (x : ℝ × ℝ) :
    (ℝ × ℝ) × Environment → (ℝ × ℝ) × Environment := fun p =>
  ((Int.fract (p.1.1 + x.1), Int.fract (p.1.2 + x.2)),
    fun z : Lattice => p.2 ((⌊p.1.1 + x.1⌋, ⌊p.1.2 + x.2⌋) + z))

/-- The random-phase array `X_{m,n}(θ, ω)`: the passage time from the lattice point
`⌊m x + θ⌋` to the lattice point `⌊n x + θ⌋`, written with integer floors so that the shift
identity below holds for every real phase. The displacement uses `Int.toNat`; it is the true
difference whenever `m ≤ n`. -/
private noncomputable def phaseArray (x : ℝ × ℝ) (m n : ℕ) (p : (ℝ × ℝ) × Environment) : ℝ :=
  lastPassage p.2 (⌊(m : ℝ) * x.1 + p.1.1⌋, ⌊(m : ℝ) * x.2 + p.1.2⌋)
    ((⌊(n : ℝ) * x.1 + p.1.1⌋ - ⌊(m : ℝ) * x.1 + p.1.1⌋).toNat,
      (⌊(n : ℝ) * x.2 + p.1.2⌋ - ⌊(m : ℝ) * x.2 + p.1.2⌋).toNat)

/-- Iterates of the skew map preserve the random-phase law. -/
private theorem measurePreserving_phaseSkew (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ × ℝ)
    (k : ℕ) : MeasurePreserving ((phaseSkew x)^[k]) (phaseLaw μ) (phaseLaw μ) :=
  (measurePreserving_phase_skew μ x).iterate k

/-- The one place where floor-dependent endpoints are handled. If the start and the
displacement depend measurably on the phase, then the passage time is measurable on the
product. The pair of endpoints takes values in a countable type, and for each fixed endpoint
the passage time is measurable in the environment (`measurable_lastPassage`). -/
private theorem measurable_phase_passage (u : ℝ × ℝ → Lattice) (d : ℝ × ℝ → ℕ × ℕ)
    (hu : Measurable u) (hd : Measurable d) :
    Measurable (fun p : (ℝ × ℝ) × Environment => lastPassage p.2 (u p.1) (d p.1)) := by
  have hF : Measurable
      (fun q : (Lattice × (ℕ × ℕ)) × Environment => lastPassage q.2 q.1.1 q.1.2) :=
    measurable_from_prod_countable_right fun e => measurable_lastPassage e.1 e.2
  exact hF.comp (((hu.comp measurable_fst).prodMk (hd.comp measurable_fst)).prodMk measurable_snd)

/-- Every entry of the array is measurable. -/
private theorem measurable_phaseArray (x : ℝ × ℝ) (m n : ℕ) : Measurable (phaseArray x m n) := by
  have h1 (k : ℕ) : Measurable (fun θ : ℝ × ℝ => ⌊(k : ℝ) * x.1 + θ.1⌋) :=
    Int.measurable_floor.comp (measurable_fst.const_add _)
  have h2 (k : ℕ) : Measurable (fun θ : ℝ × ℝ => ⌊(k : ℝ) * x.2 + θ.2⌋) :=
    Int.measurable_floor.comp (measurable_snd.const_add _)
  have hnat : Measurable Int.toNat := measurable_of_countable _
  exact measurable_phase_passage
    (fun θ : ℝ × ℝ => (⌊(m : ℝ) * x.1 + θ.1⌋, ⌊(m : ℝ) * x.2 + θ.2⌋))
    (fun θ : ℝ × ℝ => ((⌊(n : ℝ) * x.1 + θ.1⌋ - ⌊(m : ℝ) * x.1 + θ.1⌋).toNat,
      (⌊(n : ℝ) * x.2 + θ.2⌋ - ⌊(m : ℝ) * x.2 + θ.2⌋).toNat))
    ((h1 m).prodMk (h2 m))
    ((hnat.comp ((h1 n).sub (h1 m))).prodMk (hnat.comp ((h2 n).sub (h2 m))))

/-- Floor identity behind the shift: adding `x` to the phase and removing the integer part
moves the index by one. -/
private theorem floor_shift (k : ℕ) (t a : ℝ) :
    ⌊(k : ℝ) * a + Int.fract (t + a)⌋ = ⌊((k + 1 : ℕ) : ℝ) * a + t⌋ - ⌊t + a⌋ := by
  have : (k : ℝ) * a + Int.fract (t + a) = (((k + 1 : ℕ) : ℝ) * a + t) - ((⌊t + a⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [this, Int.floor_sub_intCast]

/-- Shift identity `X_{m,n} ∘ Φ = X_{m+1,n+1}`, for every phase. -/
private theorem phaseArray_comp_skew (x : ℝ × ℝ) (m n : ℕ) (p : (ℝ × ℝ) × Environment) :
    phaseArray x m n (phaseSkew x p) = phaseArray x (m + 1) (n + 1) p := by
  have h1 := floor_shift m p.1.1 x.1
  have h2 := floor_shift m p.1.2 x.2
  have h3 := floor_shift n p.1.1 x.1
  have h4 := floor_shift n p.1.2 x.2
  simp only [phaseArray, phaseSkew, lastPassage_translate, h1, h2, h3, h4]
  congr 1
  · ext <;> simp
  · ext <;> simp

/-- Iterated shift identity: `X_{m,n} ∘ Φ^k = X_{m+k,n+k}`. -/
private theorem phaseArray_comp_skew_iterate (x : ℝ × ℝ) (k m n : ℕ)
    (p : (ℝ × ℝ) × Environment) :
    phaseArray x m n ((phaseSkew x)^[k] p) = phaseArray x (m + k) (n + k) p := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (phaseSkew x p), phaseArray_comp_skew]
    rfl

/-- Superadditivity (2.2) of Martin (2004) for lattice points `a ≤ b ≤ c`, with displacements
written by `Int.toNat`. -/
private theorem lastPassage_superadditive_int (ω : Environment) (a b c : Lattice)
    (hab : a ≤ b) (hbc : b ≤ c) :
    lastPassage ω a ((b.1 - a.1).toNat, (b.2 - a.2).toNat) +
      lastPassage ω b ((c.1 - b.1).toNat, (c.2 - b.2).toNat) ≤
    lastPassage ω a ((c.1 - a.1).toNat, (c.2 - a.2).toNat) := by
  have hab' := Prod.le_def.mp hab
  have hbc' := Prod.le_def.mp hbc
  have h := lastPassage_superadditive ω a ((b.1 - a.1).toNat, (b.2 - a.2).toNat)
    ((c.1 - b.1).toNat, (c.2 - b.2).toNat)
  have e1 : a + (((b.1 - a.1).toNat : ℤ), ((b.2 - a.2).toNat : ℤ)) = b :=
    Prod.ext (by show a.1 + ((b.1 - a.1).toNat : ℤ) = b.1; omega)
      (by show a.2 + ((b.2 - a.2).toNat : ℤ) = b.2; omega)
  have e2 : ((b.1 - a.1).toNat, (b.2 - a.2).toNat) + ((c.1 - b.1).toNat, (c.2 - b.2).toNat) =
      ((c.1 - a.1).toNat, (c.2 - a.2).toNat) :=
    Prod.ext (by show (b.1 - a.1).toNat + (c.1 - b.1).toNat = (c.1 - a.1).toNat; omega)
      (by show (b.2 - a.2).toNat + (c.2 - b.2).toNat = (c.2 - a.2).toNat; omega)
  rw [e1, e2] at h
  exact h

/-- Superadditivity (2.2) of Martin (2004) for the random-phase array:
`X_{l,m} + X_{m,n} ≤ X_{l,n}` for `l ≤ m ≤ n`,
every phase. -/
private theorem phaseArray_superadditive (x : ℝ × ℝ) (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2)
    (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n) (p : (ℝ × ℝ) × Environment) :
    phaseArray x l m p + phaseArray x m n p ≤ phaseArray x l n p := by
  have mono (a θ : ℝ) (ha : 0 ≤ a) (i j : ℕ) (hij : i ≤ j) :
      ⌊(i : ℝ) * a + θ⌋ ≤ ⌊(j : ℝ) * a + θ⌋ :=
    Int.floor_le_floor (add_le_add_left (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr hij) ha) _)
  exact lastPassage_superadditive_int p.2
    (⌊(l : ℝ) * x.1 + p.1.1⌋, ⌊(l : ℝ) * x.2 + p.1.2⌋)
    (⌊(m : ℝ) * x.1 + p.1.1⌋, ⌊(m : ℝ) * x.2 + p.1.2⌋)
    (⌊(n : ℝ) * x.1 + p.1.1⌋, ⌊(n : ℝ) * x.2 + p.1.2⌋)
    (Prod.mk_le_mk.mpr ⟨mono _ _ hx1 _ _ hlm, mono _ _ hx2 _ _ hlm⟩)
    (Prod.mk_le_mk.mpr ⟨mono _ _ hx1 _ _ hmn, mono _ _ hx2 _ _ hmn⟩)

/-- On the unit square the array at index `0` is the plain passage time from the origin to
`⌊n x + θ⌋` (natural floors), which is the form of the public output. -/
private theorem phaseArray_zero_eq (x : ℝ × ℝ) (n : ℕ) (p : (ℝ × ℝ) × Environment)
    (h1 : p.1.1 ∈ Ico (0 : ℝ) 1) (h2 : p.1.2 ∈ Ico (0 : ℝ) 1) :
    phaseArray x 0 n p =
      lastPassage p.2 0 (⌊(n : ℝ) * x.1 + p.1.1⌋₊, ⌊(n : ℝ) * x.2 + p.1.2⌋₊) := by
  have e1 : ⌊p.1.1⌋ = 0 := Int.floor_eq_zero_iff.mpr h1
  have e2 : ⌊p.1.2⌋ = 0 := Int.floor_eq_zero_iff.mpr h2
  simp only [phaseArray, Nat.cast_zero, zero_mul, zero_add, e1, e2, sub_zero, Int.floor_toNat]
  rfl


/-- The uniform law on the unit square lives on the square. -/
private theorem ae_unit_square :
    ∀ᵐ θ ∂((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))),
      θ.1 ∈ Ico (0 : ℝ) 1 ∧ θ.2 ∈ Ico (0 : ℝ) 1 := by
  have hU : ∀ᵐ t ∂(volume.restrict (Ico (0 : ℝ) 1)), t ∈ Ico (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ico
  exact (measurePreserving_fst.quasiMeasurePreserving.ae hU).and
    (measurePreserving_snd.quasiMeasurePreserving.ae hU)

/-- Almost every phase of the random-phase law lies in the unit square. -/
private theorem ae_phase_mem (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ p ∂phaseLaw μ, p.1.1 ∈ Ico (0 : ℝ) 1 ∧ p.1.2 ∈ Ico (0 : ℝ) 1 :=
  measurePreserving_fst.quasiMeasurePreserving.ae ae_unit_square

/-- Integrability of `X_{0,n}`: on the unit square it is dominated
by a phase-independent sum of absolute weights over a box. -/
private theorem integrable_phaseArray_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : ℝ × ℝ) (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2) (n : ℕ) :
    Integrable (phaseArray x 0 n) (phaseLaw μ) := by
  set N : ℕ × ℕ := (⌊(n : ℝ) * x.1⌋₊ + 1, ⌊(n : ℝ) * x.2⌋₊ + 1) with hN
  set G : Environment → ℝ := fun ω => ((N.1 + N.2 : ℕ) : ℝ) *
    ∑ z ∈ Finset.Icc ((0 : ℤ), (0 : ℤ)) ((N.1 : ℤ), (N.2 : ℤ)), |ω z| with hG
  have hGi : Integrable G (environmentLaw μ) :=
    (integrable_finsetSum _ fun z _ => (integrable_environment_eval μ hμ z).abs).const_mul _
  have hGP : Integrable (fun p : (ℝ × ℝ) × Environment => G p.2) (phaseLaw μ) :=
    hGi.comp_snd _
  refine hGP.mono' (measurable_phaseArray x 0 n).aestronglyMeasurable ?_
  filter_upwards [ae_phase_mem μ] with p hp
  rw [Real.norm_eq_abs, phaseArray_zero_eq x n p hp.1 hp.2]
  exact abs_lastPassage_le_box_sum p.2 _ N
    (floor_add_phase_le_floor_add_one _ _ (mul_nonneg (Nat.cast_nonneg _) hx1) hp.1.2)
    (floor_add_phase_le_floor_add_one _ _ (mul_nonneg (Nat.cast_nonneg _) hx2) hp.2.2)


/-- Step count for the linear bound: `j ≥ 1` with `j x_i ≥ 1` wherever `x_i > 0`, and `D`
with `j x_i ≤ D`. -/
private theorem exists_step_count (x : ℝ × ℝ) (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2) :
    ∃ j D : ℕ, 0 < j ∧ (x.1 = 0 ∨ 1 ≤ (j : ℝ) * x.1) ∧ (x.2 = 0 ∨ 1 ≤ (j : ℝ) * x.2) ∧
      (j : ℝ) * x.1 ≤ D ∧ (j : ℝ) * x.2 ≤ D := by
  obtain ⟨k1, hk1⟩ := exists_nat_ge (1 / x.1)
  obtain ⟨k2, hk2⟩ := exists_nat_ge (1 / x.2)
  have hstep (y : ℝ) (hy : 0 ≤ y) (k j : ℕ) (hk : 1 / y ≤ k) (hkj : k ≤ j) :
      y = 0 ∨ 1 ≤ (j : ℝ) * y := by
    rcases hy.eq_or_lt with h0 | hpos
    · exact Or.inl h0.symm
    · refine Or.inr ?_
      have h1 : 1 ≤ (k : ℝ) * y := by
        have := (div_le_iff₀ hpos).mp hk
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkj) hy)
  obtain ⟨D, hD⟩ := exists_nat_ge (((k1 + k2 + 1 : ℕ) : ℝ) * x.1 + ((k1 + k2 + 1 : ℕ) : ℝ) * x.2)
  have hj1 : 0 ≤ ((k1 + k2 + 1 : ℕ) : ℝ) * x.1 := mul_nonneg (Nat.cast_nonneg _) hx1
  have hj2 : 0 ≤ ((k1 + k2 + 1 : ℕ) : ℝ) * x.2 := mul_nonneg (Nat.cast_nonneg _) hx2
  exact ⟨k1 + k2 + 1, D, Nat.succ_pos _, hstep x.1 hx1 k1 _ hk1 (by omega),
    hstep x.2 hx2 k2 _ hk2 (by omega), by linarith, by linarith⟩

/-- Environment mean of the passage time to `⌊n x + θ⌋` for a phase in the unit square, from
corrected monotonicity and the linear bound at index `n + j`. -/
private theorem inner_mean_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) (g : EReal)
    (hg : Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ)) : ℝ) : EReal)) atTop (𝓝 g))
    (hgtop : g ≠ ⊤) (θ : ℝ × ℝ) (hθ1 : θ.1 ∈ Ico (0 : ℝ) 1) (hθ2 : θ.2 ∈ Ico (0 : ℝ) 1)
    (n j D : ℕ) (hj : 0 < j)
    (hj1 : (x.1 : ℝ) = 0 ∨ 1 ≤ (j : ℝ) * (x.1 : ℝ))
    (hj2 : (x.2 : ℝ) = 0 ∨ 1 ≤ (j : ℝ) * (x.2 : ℝ))
    (hD1 : (j : ℝ) * (x.1 : ℝ) ≤ D) (hD2 : (j : ℝ) * (x.2 : ℝ) ≤ D) :
    (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ) + θ.1⌋₊, ⌊(n : ℝ) * (x.2 : ℝ) + θ.2⌋₊) ∂environmentLaw μ) ≤
      ((n + j : ℕ) : ℝ) * g.toReal + 2 * |∫ t : ℝ, t ∂μ| + 2 * D * |∫ t : ℝ, t ∂μ| := by
  have hab : ⌊(n : ℝ) * (x.1 : ℝ) + θ.1⌋₊ ≤ ⌊((n + j : ℕ) : ℝ) * (x.1 : ℝ)⌋₊ ∧
      ⌊(n : ℝ) * (x.2 : ℝ) + θ.2⌋₊ ≤ ⌊((n + j : ℕ) : ℝ) * (x.2 : ℝ)⌋₊ := Prod.le_def.mp (floor_phase_le_floor ((x.1 : ℝ), (x.2 : ℝ)) θ j n
    ⟨hθ1.1, hθ1.2⟩ ⟨hθ2.1, hθ2.2⟩ hj1 hj2)
  have hgap : ⌊((n + j : ℕ) : ℝ) * (x.1 : ℝ)⌋₊ ≤ ⌊(n : ℝ) * (x.1 : ℝ) + θ.1⌋₊ + D ∧
      ⌊((n + j : ℕ) : ℝ) * (x.2 : ℝ)⌋₊ ≤ ⌊(n : ℝ) * (x.2 : ℝ) + θ.2⌋₊ + D := floor_phase_gap_le ((x.1 : ℝ), (x.2 : ℝ)) θ j n D (NNReal.coe_nonneg _)
    (NNReal.coe_nonneg _) hθ1.1 hθ2.1 hD1 hD2
  have hmono := integral_lastPassage_corrected_monotone μ hμ
    (⌊(n : ℝ) * (x.1 : ℝ) + θ.1⌋₊, ⌊(n : ℝ) * (x.2 : ℝ) + θ.2⌋₊)
    (⌊((n + j : ℕ) : ℝ) * (x.1 : ℝ)⌋₊, ⌊((n + j : ℕ) : ℝ) * (x.2 : ℝ)⌋₊) hab.1 hab.2
  have hlin := expected_floor_rate_ereal_linear_bound μ hμ x g hg hgtop (n + j) (by omega)
  have hle : ((⌊(n : ℝ) * (x.1 : ℝ) + θ.1⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ) + θ.2⌋₊ : ℕ) : ℝ) ≤
      ((⌊((n + j : ℕ) : ℝ) * (x.1 : ℝ)⌋₊ + ⌊((n + j : ℕ) : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add hab.1 hab.2
  have hge : ((⌊((n + j : ℕ) : ℝ) * (x.1 : ℝ)⌋₊ + ⌊((n + j : ℕ) : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) ≤
      ((⌊(n : ℝ) * (x.1 : ℝ) + θ.1⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ) + θ.2⌋₊ : ℕ) : ℝ) + 2 * D := by
    have : ⌊((n + j : ℕ) : ℝ) * (x.1 : ℝ)⌋₊ + ⌊((n + j : ℕ) : ℝ) * (x.2 : ℝ)⌋₊ ≤
        ⌊(n : ℝ) * (x.1 : ℝ) + θ.1⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ) + θ.2⌋₊ + 2 * D := by
      have := hgap.1
      have := hgap.2
      omega
    exact_mod_cast this
  generalize (∫ t : ℝ, t ∂μ) = m at hmono hlin ⊢
  generalize ((⌊(n : ℝ) * (x.1 : ℝ) + θ.1⌋₊ + ⌊(n : ℝ) * (x.2 : ℝ) + θ.2⌋₊ : ℕ) : ℝ) = sa
    at hmono hle hge
  generalize ((⌊((n + j : ℕ) : ℝ) * (x.1 : ℝ)⌋₊ + ⌊((n + j : ℕ) : ℝ) * (x.2 : ℝ)⌋₊ : ℕ) : ℝ) = sb
    at hmono hle hge
  have h0 : 0 ≤ sb - sa := by linarith
  have h1 : (sb - sa) * |m| ≤ 2 * D * |m| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg m)
  have h2 : 0 ≤ (sb - sa) * (|m| + m) := mul_nonneg h0 (by linarith [neg_abs_le m])
  nlinarith [h1, h2, hmono, hlin]


/-- Linear upper bound `∫ X_{0,n} ≤ c n` for all `n ≥ 1`, by integrating the bound over the
phase. -/
private theorem phaseArray_mean_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) (g : EReal)
    (hg : Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ)) : ℝ) : EReal)) atTop (𝓝 g))
    (hgtop : g ≠ ⊤) :
    ∃ c : ℝ, ∀ n : ℕ, 0 < n →
      ∫ p, phaseArray ((x.1 : ℝ), (x.2 : ℝ)) 0 n p ∂phaseLaw μ ≤ c * n := by
  obtain ⟨j, D, hj, hj1, hj2, hD1, hD2⟩ :=
    exists_step_count ((x.1 : ℝ), (x.2 : ℝ)) (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  refine ⟨(1 + j) * |g.toReal| + (2 + 2 * D) * |∫ t : ℝ, t ∂μ|, fun n hn => ?_⟩
  have hint := integrable_phaseArray_zero μ hμ ((x.1 : ℝ), (x.2 : ℝ)) (NNReal.coe_nonneg _)
    (NNReal.coe_nonneg _) n
  have hinner : ∀ᵐ θ ∂((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))),
      (∫ ω : Environment, phaseArray ((x.1 : ℝ), (x.2 : ℝ)) 0 n (θ, ω) ∂environmentLaw μ) ≤
        ((n + j : ℕ) : ℝ) * g.toReal + 2 * |∫ t : ℝ, t ∂μ| + 2 * D * |∫ t : ℝ, t ∂μ| := by
    filter_upwards [ae_unit_square] with θ hθ
    have hrew : ∀ ω : Environment, phaseArray ((x.1 : ℝ), (x.2 : ℝ)) 0 n (θ, ω) =
        lastPassage ω 0 (⌊(n : ℝ) * (x.1 : ℝ) + θ.1⌋₊, ⌊(n : ℝ) * (x.2 : ℝ) + θ.2⌋₊) :=
      fun ω => phaseArray_zero_eq ((x.1 : ℝ), (x.2 : ℝ)) n (θ, ω) hθ.1 hθ.2
    simp only [hrew]
    exact inner_mean_le μ hμ x g hg hgtop θ hθ.1 hθ.2 n j D hj hj1 hj2 hD1 hD2
  have hmean : (∫ p, phaseArray ((x.1 : ℝ), (x.2 : ℝ)) 0 n p ∂phaseLaw μ) ≤
      ((n + j : ℕ) : ℝ) * g.toReal + 2 * |∫ t : ℝ, t ∂μ| + 2 * D * |∫ t : ℝ, t ∂μ| := by
    rw [phaseLaw, integral_prod _ hint]
    refine (integral_mono_ae hint.integral_prod_left (integrable_const _) hinner).trans ?_
    simp
  refine hmean.trans ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 := abs_nonneg (∫ t : ℝ, t ∂μ)
  have hg0 := abs_nonneg g.toReal
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hgle : ((n + j : ℕ) : ℝ) * g.toReal ≤ (n * (1 + j) : ℝ) * |g.toReal| := by
    calc ((n + j : ℕ) : ℝ) * g.toReal ≤ ((n + j : ℕ) : ℝ) * |g.toReal| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg _)
      _ ≤ (n * (1 + j) : ℝ) * |g.toReal| := by
          apply mul_le_mul_of_nonneg_right _ hg0
          push_cast
          nlinarith
  have hmle : 2 * |∫ t : ℝ, t ∂μ| + 2 * D * |∫ t : ℝ, t ∂μ| ≤
      (n : ℝ) * ((2 + 2 * D) * |∫ t : ℝ, t ∂μ|) := by
    have : 0 ≤ (2 + 2 * (D : ℝ)) * |∫ t : ℝ, t ∂μ| := by positivity
    nlinarith
  nlinarith


/-- Composing a sequence with a measure-preserving map keeps its joint law. -/
private theorem identDistrib_comp_of_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T P P) {f : Ω → ℕ → ℝ}
    (hf : Measurable f) : IdentDistrib (fun ω => f (T ω)) f P P :=
  ⟨(hf.comp hT.measurable).aemeasurable, hf.aemeasurable, by
    show Measure.map (f ∘ T) P = Measure.map f P
    rw [← Measure.map_map hf hT.measurable, hT.map_eq]⟩

/-- A sequence of negated array entries is a measurable map into sequences. -/
private theorem measurable_phaseArray_sequence (x : ℝ × ℝ) (a b : ℕ → ℕ) :
    Measurable (fun p : (ℝ × ℝ) × Environment => fun j : ℕ => -phaseArray x (a j) (b j) p) :=
  measurable_pi_iff.mpr fun j => (measurable_phaseArray x (a j) (b j)).neg

/-- Random-phase limit for Martin (2004), Proposition 2.1 in a non-lattice direction (Martin gives
no argument there). Let the weight law `μ` have a finite mean, let `x` be a direction, and suppose
the expected floor rate `E T(⌊n x⌋) / n` tends to `g` with `g ≠ +∞`. Give each point a uniform phase
`θ` in the unit square and write `T_n(θ, ω)` for the passage time from the origin to
`(⌊n x₁ + θ₁⌋, ⌊n x₂ + θ₂⌋)`. Then on the product of the phase law and the environment law there is
a measurable integrable `Y` with `T_n / n → Y` almost surely and in L1. The proof applies Liggett's
theorem to the negative of the random-phase array. -/
theorem exists_random_phase_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : Quadrant) (g : EReal)
    (hg : Tendsto (fun n : ℕ => ((((∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊) ∂environmentLaw μ) /
        (n : ℝ)) : ℝ) : EReal)) atTop (𝓝 g))
    (hgtop : g ≠ ⊤) :
    ∃ Y : (ℝ × ℝ) × Environment → ℝ, Measurable Y ∧
      Integrable Y (((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))).prod
        (environmentLaw μ)) ∧
      (∀ᵐ p ∂(((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))).prod
          (environmentLaw μ)),
        Tendsto (fun n : ℕ => lastPassage p.2 0
          (⌊(n : ℝ) * (x.1 : ℝ) + p.1.1⌋₊, ⌊(n : ℝ) * (x.2 : ℝ) + p.1.2⌋₊) / (n : ℝ))
          atTop (𝓝 (Y p))) ∧
      Tendsto (fun n : ℕ => ∫ p, |lastPassage p.2 0
          (⌊(n : ℝ) * (x.1 : ℝ) + p.1.1⌋₊, ⌊(n : ℝ) * (x.2 : ℝ) + p.1.2⌋₊) / (n : ℝ) - Y p|
          ∂(((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))).prod
            (environmentLaw μ))) atTop (𝓝 0) := by
  set x' : ℝ × ℝ := ((x.1 : ℝ), (x.2 : ℝ)) with hx'
  have hx1 : 0 ≤ x'.1 := NNReal.coe_nonneg _
  have hx2 : 0 ≤ x'.2 := NNReal.coe_nonneg _
  obtain ⟨c, hc⟩ := phaseArray_mean_le μ hμ x g hg hgtop
  have hadj : ∀ m : ℕ, ProbabilityTheory.IdentDistrib
      (fun p (j : ℕ) => -phaseArray x' (m + 1) (m + 1 + (j + 1)) p)
      (fun p (j : ℕ) => -phaseArray x' m (m + (j + 1)) p) (phaseLaw μ) (phaseLaw μ) := by
    intro m
    have hfun : (fun p (j : ℕ) => -phaseArray x' (m + 1) (m + 1 + (j + 1)) p) =
        fun p => (fun p' (j : ℕ) => -phaseArray x' m (m + (j + 1)) p') (phaseSkew x' p) := by
      funext p j
      beta_reduce
      rw [phaseArray_comp_skew]
      congr 2
      omega
    rw [hfun]
    exact identDistrib_comp_of_measurePreserving
      (by simpa using measurePreserving_phaseSkew μ x' 1)
      (measurable_phaseArray_sequence x' (fun _ => m) (fun j => m + (j + 1)))
  have hstat : ∀ k : ℕ, 0 < k → ProbabilityTheory.IdentDistrib
      (fun p (j : ℕ) => -phaseArray x' ((j + 2) * k) ((j + 3) * k) p)
      (fun p (j : ℕ) => -phaseArray x' ((j + 1) * k) ((j + 2) * k) p) (phaseLaw μ) (phaseLaw μ) := by
    intro k _
    have hfun : (fun p (j : ℕ) => -phaseArray x' ((j + 2) * k) ((j + 3) * k) p) =
        fun p => (fun p' (j : ℕ) => -phaseArray x' ((j + 1) * k) ((j + 2) * k) p')
          ((phaseSkew x')^[k] p) := by
      funext p j
      beta_reduce
      rw [phaseArray_comp_skew_iterate]
      congr 3 <;> ring
    rw [hfun]
    exact identDistrib_comp_of_measurePreserving (measurePreserving_phaseSkew μ x' k)
      (measurable_phaseArray_sequence x' (fun j => (j + 1) * k) (fun j => (j + 2) * k))
  obtain ⟨γ, G, hGm, hGi, hGae, -, -, -, hGL1⟩ := exists_liggett_convergence (phaseLaw μ)
    (fun m n p => -phaseArray x' m n p)
    (fun n _ => (measurable_phaseArray x' 0 n).neg)
    (fun n _ => (integrable_phaseArray_zero μ hμ x' hx1 hx2 n).neg) c
    (fun n hn => by
      rw [integral_neg]
      linarith [hc n hn])
    (fun m n _ hmn => Filter.Eventually.of_forall fun p => by
      have := phaseArray_superadditive x' hx1 hx2 0 m n (Nat.zero_le _) hmn.le p
      show -phaseArray x' 0 n p ≤ -phaseArray x' 0 m p + -phaseArray x' m n p
      linarith)
    hadj hstat
  refine ⟨fun p => -G p, hGm.neg, hGi.neg, ?_, ?_⟩
  · filter_upwards [hGae, ae_phase_mem μ] with p hp hph
    have hp' : Tendsto (fun n : ℕ => -phaseArray x' 0 (n + 1) p / ((n + 1 : ℕ) : ℝ)) atTop
        (𝓝 (G p)) := hp
    refine (tendsto_add_atTop_iff_nat 1).mp (hp'.neg.congr fun n => ?_)
    rw [phaseArray_zero_eq x' (n + 1) p hph.1 hph.2, neg_div, neg_neg]
  · have hL1 : Tendsto (fun n : ℕ => ∫ p, |-phaseArray x' 0 (n + 1) p / ((n + 1 : ℕ) : ℝ) - G p|
        ∂phaseLaw μ) atTop (𝓝 0) := hGL1
    refine (tendsto_add_atTop_iff_nat 1).mp (hL1.congr fun n => ?_)
    refine integral_congr_ae ?_
    filter_upwards [ae_phase_mem μ] with p hph
    rw [phaseArray_zero_eq x' (n + 1) p hph.1 hph.2]
    rw [← abs_neg]
    congr 1
    ring

end LPPDifferentiability
