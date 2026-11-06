/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.StationaryRowStep

/-!
# Stationarity of the row increments of the exponential corner growth model

Two inductions establish the row stationarity result.

* The row identity (deterministic). The row map of `Probability/BurkeRow.lean`, applied to the
  horizontal increments of row `n` from column `i₀`, the vertical increment at column `i₀` and the
  bulk weights at height `n + 1`, returns the increments of row `n + 1` and the vertical
  increment `M` columns further on. Induction on the row length `M`, with the starting column
  `i₀` free: the first cell is the cell identity at column `i₀`, and the rest of the row is the
  same statement from column `i₀ + 1`.
* The law of a row. Under i.i.d. `Exp(1)` weights, the first `M` horizontal increments of row
  `n` are i.i.d. `Exp(1 - ρ)`. Induction on `n`. Row `0` is the weights on the horizontal axis
  divided by `1 - ρ`. For the step, row `n` is a function of the weights on the box below
  height `n + 1`, and the boundary and bulk inputs are functions of the weights at height
  `n + 1`, so they are independent; the row lemma `map_stationaryRowMap` gives row `n + 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-! ## The row identity -/

/-- One more cell of the row map: if the tails of the inputs are the inputs `a'`, `c'` of a row
of length `M`, the carried value after the first cell is `y`, the first output is `x`, and the
row of length `M` sends `(a', y, c')` to `(A', B')`, then the row map of length `M + 1` sends
`(a, b, c)` to `(x :: A', B')`. -/
private theorem stationaryRowMap_succ_eq {M : ℕ} {a c : Fin (M + 1) → ℝ} {b : ℝ}
    {a' c' : Fin M → ℝ} {x y B' : ℝ} {A' : Fin M → ℝ}
    (ha : Fin.tail a = a') (hc : Fin.tail c = c')
    (hy : c 0 + max (b - a 0) 0 = y) (hx : c 0 + max (a 0 - b) 0 = x)
    (hrest : stationaryRowMap M a' y c' = (A', B')) :
    stationaryRowMap (M + 1) a b c = (Fin.cons x A', B') := by
  subst ha hc hy hx
  have h : stationaryRowMap (M + 1) a b c =
      (Fin.cons (c 0 + max (a 0 - b) 0)
          (stationaryRowMap M (Fin.tail a) (c 0 + max (b - a 0) 0) (Fin.tail c)).1,
        (stationaryRowMap M (Fin.tail a) (c 0 + max (b - a 0) 0) (Fin.tail c)).2) := rfl
  rw [h, hrest]

/-- **Row map identity in offset form.** By induction on `M`, the row map applied to
the increments of row `n` from column `i₀` on, the vertical increment at column `i₀` and the
bulk weights at height `n + 1` gives row `n + 1` from column `i₀` on and the vertical increment
at column `i₀ + M`. The tail of the row map starts one column later, so `i₀` is generalized. -/
theorem stationaryRowMap_stationaryIncrements_offset (ρ : ℝ) (ω : Environment)
    (i₀ n M : ℕ) :
    stationaryRowMap M (fun i : Fin M => stationaryHorizontalIncrement ρ ω (i₀ + (i : ℕ)) n)
        (stationaryVerticalIncrement ρ ω i₀ n)
        (fun i : Fin M => ω (((i₀ + (i : ℕ) : ℕ) : ℤ) + 1, (n : ℤ) + 1)) =
      (fun i : Fin M => stationaryHorizontalIncrement ρ ω (i₀ + (i : ℕ)) (n + 1),
        stationaryVerticalIncrement ρ ω (i₀ + M) n) := by
  induction M generalizing i₀ with
  | zero =>
    refine Prod.ext (funext fun i => i.elim0) ?_
    rfl
  | succ M ih =>
    -- the first cell of the row, at column `i₀`
    have hcellH := stationaryHorizontalIncrement_succ ρ ω i₀ n
    have hcellV := stationaryVerticalIncrement_succ ρ ω i₀ n
    -- the output row, written as the first output followed by the outputs of the later cells
    have hR : ((fun i : Fin (M + 1) => stationaryHorizontalIncrement ρ ω (i₀ + (i : ℕ)) (n + 1)),
          stationaryVerticalIncrement ρ ω (i₀ + (M + 1)) n) =
        (Fin.cons (stationaryHorizontalIncrement ρ ω i₀ (n + 1))
            (fun i : Fin M => stationaryHorizontalIncrement ρ ω (i₀ + 1 + (i : ℕ)) (n + 1)),
          stationaryVerticalIncrement ρ ω (i₀ + 1 + M) n) := by
      rw [Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · funext i
        induction i using Fin.cases with
        | zero => simp
        | succ j =>
          rw [Fin.cons_succ]
          show stationaryHorizontalIncrement ρ ω (i₀ + ((j.succ : Fin (M + 1)) : ℕ)) (n + 1) =
            stationaryHorizontalIncrement ρ ω (i₀ + 1 + (j : ℕ)) (n + 1)
          rw [Fin.val_succ]
          congr 1
          omega
      · show stationaryVerticalIncrement ρ ω (i₀ + (M + 1)) n =
          stationaryVerticalIncrement ρ ω (i₀ + 1 + M) n
        congr 1
        omega
    rw [hR]
    refine stationaryRowMap_succ_eq (a' := fun i : Fin M =>
        stationaryHorizontalIncrement ρ ω (i₀ + 1 + (i : ℕ)) n)
      (c' := fun i : Fin M => ω (((i₀ + 1 + (i : ℕ) : ℕ) : ℤ) + 1, (n : ℤ) + 1))
      (y := stationaryVerticalIncrement ρ ω (i₀ + 1) n) ?_ ?_ ?_ ?_ (ih (i₀ + 1))
    · funext i
      show stationaryHorizontalIncrement ρ ω (i₀ + ((i.succ : Fin (M + 1)) : ℕ)) n =
        stationaryHorizontalIncrement ρ ω (i₀ + 1 + (i : ℕ)) n
      rw [Fin.val_succ]
      congr 1
      omega
    · funext i
      have h : i₀ + ((i.succ : Fin (M + 1)) : ℕ) = i₀ + 1 + (i : ℕ) := by
        rw [Fin.val_succ]
        omega
      show ω (((i₀ + ((i.succ : Fin (M + 1)) : ℕ) : ℕ) : ℤ) + 1, (n : ℤ) + 1) =
        ω (((i₀ + 1 + (i : ℕ) : ℕ) : ℤ) + 1, (n : ℤ) + 1)
      rw [h]
    · simpa using hcellV.symm
    · simpa using hcellH.symm

/-- **Row map identity.** Row `n + 1` is the row map applied to row `n`, the vertical increment
at column `0` and the bulk weights at height `n + 1`; the case `i₀ = 0` of the offset form. -/
theorem stationaryRowMap_stationaryIncrements (ρ : ℝ) (ω : Environment) (n M : ℕ) :
    stationaryRowMap M (fun i : Fin M => stationaryHorizontalIncrement ρ ω i n)
        (stationaryVerticalIncrement ρ ω 0 n)
        (fun i : Fin M => ω ((i.val : ℤ) + 1, (n : ℤ) + 1)) =
      (fun i : Fin M => stationaryHorizontalIncrement ρ ω i (n + 1),
        stationaryVerticalIncrement ρ ω M n) := by
  simpa only [Nat.zero_add] using stationaryRowMap_stationaryIncrements_offset ρ ω 0 n M

/-! ## The law of one row -/

/-- **Stationarity.** Under the i.i.d. Exp(1) law, the increments of every row are i.i.d.
Exp(1 - ρ). The induction on the row number `n` starts from row `0`, whose increments are the
axis weights divided by `1 - ρ`. Row `n + 1` is the row map of row `n`, the boundary weight over `ρ`
and the bulk weights at height `n + 1`; these inputs are independent because their site sets are
disjoint. -/
theorem map_stationaryHorizontalIncrements {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (n M : ℕ) :
    (environmentLaw (expMeasure 1)).map
        (fun ω : Environment => fun i : Fin M => stationaryHorizontalIncrement ρ ω i n) =
      Measure.pi fun _ : Fin M => expMeasure (1 - ρ) := by
  induction n with
  | zero =>
    -- base case: row `0` is the axis weights divided by `1 - ρ`
    have hρ' : 0 < 1 - ρ := by linarith
    have he : Function.Injective (fun i : Fin M => ((((i : ℕ) : ℤ) + 1, (0 : ℤ)) : Lattice)) := by
      intro a b hab
      have h : (((a : ℕ) : ℤ) + 1) = ((b : ℕ) : ℤ) + 1 := congrArg Prod.fst hab
      exact Fin.ext (by omega)
    have hlaw := map_environment_siteVector he
    have hmeas : Measurable (fun ω : Environment => fun i : Fin M => ω (((i : ℕ) : ℤ) + 1, 0)) :=
      measurable_pi_iff.2 fun i => measurable_environment_eval _
    have hdiv : Measurable (fun v : Fin M → ℝ => fun i : Fin M => v i / (1 - ρ)) :=
      measurable_pi_iff.2 fun i => by
        have hi : Measurable (fun v : Fin M → ℝ => v i) := measurable_pi_apply i
        exact hi.div_const (1 - ρ)
    have hfun : (fun ω : Environment => fun i : Fin M => stationaryHorizontalIncrement ρ ω i 0) =
        (fun v : Fin M → ℝ => fun i : Fin M => v i / (1 - ρ)) ∘
          (fun ω : Environment => fun i : Fin M => ω (((i : ℕ) : ℤ) + 1, 0)) := by
      funext ω i
      exact (stationaryIncrement_boundary ρ ω i 0).1
    rw [hfun, ← Measure.map_map hdiv hmeas, hlaw]
    refine (Measure.pi_map_pi (μ := fun _ : Fin M => expMeasure 1)
      (f := fun _ => fun t : ℝ => t / (1 - ρ))
      (fun i => (measurable_id.div_const (1 - ρ)).aemeasurable)).trans ?_
    simp only [expMeasure_one_map_div hρ']
  | succ n ih =>
    -- the row at height `n` and the row at height `n + 1` as observables of disjoint boxes
    obtain ⟨f, hf, hfeq⟩ := exists_measurable_row_observable ρ M n
    obtain ⟨T, g, hg, hT, hgeq⟩ := exists_measurable_boundaryBulk_observable ρ M n
    have hdisj : Disjoint (Finset.Icc (0 : Lattice) ((M : ℤ), (n : ℤ))) T := by
      rw [Finset.disjoint_left]
      intro z hzS hzT
      have h1 : z.2 ≤ (n : ℤ) := (Prod.le_def.1 (Finset.mem_Icc.1 hzS).2).2
      have h2 := hT z hzT
      omega
    have hind := indepFun_environment_observables (expMeasure 1)
      (Finset.Icc (0 : Lattice) ((M : ℤ), (n : ℤ))) T hdisj hf hg
    have hRow : (fun ω : Environment => f (fun s => ω s.val)) =
        fun ω : Environment => fun i : Fin M => stationaryHorizontalIncrement ρ ω i n :=
      funext fun ω => (hfeq ω).symm
    have hY : (fun ω : Environment => g (fun t => ω t.val)) =
        fun ω : Environment =>
          (ω (0, (n : ℤ) + 1) / ρ, fun i : Fin M => ω (((i : ℕ) : ℤ) + 1, (n : ℤ) + 1)) :=
      funext fun ω => (hgeq ω).symm
    rw [hRow, hY] at hind
    have hRowm : Measurable
        (fun ω : Environment => fun i : Fin M => stationaryHorizontalIncrement ρ ω i n) :=
      measurable_pi_iff.2 fun i => measurable_stationaryHorizontalIncrement ρ i n
    have hYm : Measurable (fun ω : Environment =>
        (ω (0, (n : ℤ) + 1) / ρ, fun i : Fin M => ω (((i : ℕ) : ℤ) + 1, (n : ℤ) + 1))) :=
      ((measurable_environment_eval _).div_const ρ).prodMk
        (measurable_pi_iff.2 fun i => measurable_environment_eval _)
    have hpairm := hRowm.prodMk hYm
    -- independence gives the product law of (row `n`, boundary and bulk inputs)
    have hprod := (indepFun_iff_map_prod_eq_prod_map_map hRowm.aemeasurable
      hYm.aemeasurable).1 hind
    rw [ih, map_boundaryBulk hρ0 M n] at hprod
    -- the row map is the row identity, pointwise
    have hpt : (fun ω : Environment => stationaryRowMap M
          (fun i : Fin M => stationaryHorizontalIncrement ρ ω i n)
          (ω (0, (n : ℤ) + 1) / ρ) (fun i : Fin M => ω (((i : ℕ) : ℤ) + 1, (n : ℤ) + 1))) =
        fun ω : Environment => (fun i : Fin M => stationaryHorizontalIncrement ρ ω i (n + 1),
          stationaryVerticalIncrement ρ ω M n) := by
      funext ω
      rw [← (stationaryIncrement_boundary ρ ω 0 n).2]
      exact stationaryRowMap_stationaryIncrements ρ ω n M
    have hcomp : (fun ω : Environment => (fun i : Fin M => stationaryHorizontalIncrement ρ ω i
          (n + 1), stationaryVerticalIncrement ρ ω M n)) =
        (fun p : (Fin M → ℝ) × ℝ × (Fin M → ℝ) => stationaryRowMap M p.1 p.2.1 p.2.2) ∘
          (fun ω : Environment => (fun i : Fin M => stationaryHorizontalIncrement ρ ω i n,
            (ω (0, (n : ℤ) + 1) / ρ,
              fun i : Fin M => ω (((i : ℕ) : ℤ) + 1, (n : ℤ) + 1)))) :=
      (funext fun ω => congrFun hpt ω).symm
    have hjm : Measurable (fun ω : Environment => (fun i : Fin M =>
        stationaryHorizontalIncrement ρ ω i (n + 1), stationaryVerticalIncrement ρ ω M n)) := by
      rw [hcomp]
      exact (measurable_stationaryRowMap M).comp hpairm
    -- the row lemma gives the joint law of (row `n + 1`, last vertical increment)
    have hjoint : (environmentLaw (expMeasure 1)).map (fun ω : Environment =>
        (fun i : Fin M => stationaryHorizontalIncrement ρ ω i (n + 1),
          stationaryVerticalIncrement ρ ω M n)) =
        (Measure.pi fun _ : Fin M => expMeasure (1 - ρ)).prod (expMeasure ρ) := by
      rw [hcomp, ← Measure.map_map (measurable_stationaryRowMap M) hpairm, hprod]
      exact map_stationaryRowMap hρ0 hρ1 M
    -- the first coordinate of the joint law is the law of row `n + 1`
    have hfst : (fun ω : Environment => fun i : Fin M =>
        stationaryHorizontalIncrement ρ ω i (n + 1)) =
        Prod.fst ∘ (fun ω : Environment => (fun i : Fin M =>
          stationaryHorizontalIncrement ρ ω i (n + 1), stationaryVerticalIncrement ρ ω M n)) :=
      rfl
    have := isProbabilityMeasure_expMeasure hρ0
    rw [hfst, ← Measure.map_map measurable_fst hjm, hjoint, Measure.map_fst_prod, measure_univ,
      one_smul]

end LPPDifferentiability
