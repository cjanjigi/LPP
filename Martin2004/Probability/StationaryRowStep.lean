/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Model.LastPassage.Stationary
public import Martin2004.Probability.BurkeRow
public import LPP_Foundations.Probability.DisjointSupport
public import Martin2004.Probability.ExponentialLaw
public import LPP_Foundations.Probability.PassageMeasurable

/-!
# Helpers for the stationary increments: locality, measurability and laws of site vectors

The law of one row of horizontal increments is proved by induction on the row number. The step
needs three facts that are not about the row map itself, and this file proves them.

* Locality: the stationary passage time to `(m, n)` and the horizontal increments of row `n`
  depend only on the weights on the rectangle from `0` to `(M, n)`. Hence the row is a
  measurable function of the weights on that finite box.
* The weights at the `M + 1` sites `(0, n + 1), ..., (M, n + 1)` form a vector of independent
  `Exp(1)` variables. After dividing the first by `ρ`, the pair (boundary input, bulk weights)
  has law `Exp(ρ)` times `Exp(1)^M`.
* The weights at any injective family of sites are independent `Exp(1)`.

All statements are theorems; nothing here defines a new notion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-! ## Measurability -/

/-- The stationary environment is a measurable function of the environment: each coordinate is
the weight at one site divided by a fixed rate. -/
theorem measurable_stationaryEnvironment (ρ : ℝ) : Measurable (stationaryEnvironment ρ) :=
  measurable_pi_iff.2 fun z => by
    show Measurable fun x : Environment => x z / stationaryRate ρ z
    exact (measurable_environment_eval z).div_const (stationaryRate ρ z)

/-- For fixed `m` and `n`, the stationary passage time is a measurable function of the
environment. -/
theorem measurable_stationaryPassage (ρ : ℝ) (m n : ℕ) :
    Measurable (fun ω : Environment => stationaryPassage ρ ω m n) := by
  unfold stationaryPassage inclusivePassage
  have hend : Measurable (fun ω : Environment =>
      stationaryEnvironment ρ ω ((0 : Lattice) + ((m : ℤ), (n : ℤ)))) :=
    (measurable_pi_apply ((0 : Lattice) + ((m : ℤ), (n : ℤ)))).comp
      (measurable_stationaryEnvironment ρ)
  exact ((measurable_lastPassage 0 (m, n)).comp (measurable_stationaryEnvironment ρ)).add hend

/-- For fixed `i` and `n`, the horizontal increment is a measurable function of the
environment. -/
theorem measurable_stationaryHorizontalIncrement (ρ : ℝ) (i n : ℕ) :
    Measurable (fun ω : Environment => stationaryHorizontalIncrement ρ ω i n) :=
  (measurable_stationaryPassage ρ (i + 1) n).sub (measurable_stationaryPassage ρ i n)

/-! ## Locality -/

/-- Locality of the stationary passage time: two environments that agree on the rectangle from
`0` to `(m, n)` give the same passage time to `(m, n)`. The stationary environments agree on
the rectangle because each site is divided by the same rate; the end weight is a point of the
rectangle. -/
theorem stationaryPassage_eq_of_eqOn {ρ : ℝ} {ω η : Environment} {m n : ℕ}
    (h : ∀ z : Lattice, 0 ≤ z → z ≤ ((m : ℤ), (n : ℤ)) → ω z = η z) :
    stationaryPassage ρ ω m n = stationaryPassage ρ η m n := by
  have hst : Set.EqOn (stationaryEnvironment ρ ω) (stationaryEnvironment ρ η)
      (Set.Icc (0 : Lattice) ((0 : Lattice) + ((m : ℤ), (n : ℤ)))) := by
    intro z hz
    rw [zero_add] at hz
    show ω z / stationaryRate ρ z = η z / stationaryRate ρ z
    rw [h z hz.1 hz.2]
  have hmem : (0 : Lattice) + ((m : ℤ), (n : ℤ)) ∈
      Set.Icc (0 : Lattice) ((0 : Lattice) + ((m : ℤ), (n : ℤ))) :=
    Set.right_mem_Icc.2 (by
      rw [zero_add]
      exact Prod.le_def.2 ⟨Int.natCast_nonneg m, Int.natCast_nonneg n⟩)
  have hlast := lastPassage_eq_of_eqOn (u := (0 : Lattice)) (d := (m, n)) hst
  have hend := hst hmem
  unfold stationaryPassage inclusivePassage
  rw [hlast]
  exact congrArg _ hend

/-- Locality of the horizontal increments: if two environments agree on the rectangle from `0`
to `(M, n)`, the horizontal increments `i` of row `n` agree for every column `i < M`. -/
theorem stationaryHorizontalIncrement_eq_of_eqOn {ρ : ℝ} {ω η : Environment} {M n i : ℕ}
    (hi : i < M) (h : ∀ z : Lattice, 0 ≤ z → z ≤ ((M : ℤ), (n : ℤ)) → ω z = η z) :
    stationaryHorizontalIncrement ρ ω i n = stationaryHorizontalIncrement ρ η i n := by
  have hcol : ∀ m : ℕ, m ≤ M → stationaryPassage ρ ω m n = stationaryPassage ρ η m n := by
    intro m hm
    refine stationaryPassage_eq_of_eqOn fun z h0 h1 => h z h0 (h1.trans ?_)
    exact Prod.le_def.2 ⟨show (m : ℤ) ≤ (M : ℤ) from by exact_mod_cast hm, le_rfl⟩
  unfold stationaryHorizontalIncrement
  rw [hcol (i + 1) (Nat.succ_le_of_lt hi), hcol i hi.le]

/-- The row of horizontal increments of row `n` (columns `0, ..., M - 1`) is a measurable
function of the weights on the finite box from `0` to `(M, n)`. The function is the row of
increments of the environment that copies the box and is `0` elsewhere; locality shows that
this agrees with the row of the original environment. -/
theorem exists_measurable_row_observable (ρ : ℝ) (M n : ℕ) :
    ∃ f : ({z : Lattice // z ∈ Finset.Icc (0 : Lattice) ((M : ℤ), (n : ℤ))} → ℝ) →
        (Fin M → ℝ),
      Measurable f ∧ ∀ ω : Environment,
        (fun i : Fin M => stationaryHorizontalIncrement ρ ω i n) = f (fun s => ω s.val) := by
  let S : Finset Lattice := Finset.Icc (0 : Lattice) ((M : ℤ), (n : ℤ))
  let ext : ({z : Lattice // z ∈ S} → ℝ) → Environment :=
    fun x z => if hz : z ∈ S then x ⟨z, hz⟩ else 0
  have hext : Measurable ext := by
    refine measurable_pi_iff.2 fun z => ?_
    by_cases hz : z ∈ S
    · simp only [ext, hz, ↓reduceDIte]
      exact measurable_pi_apply _
    · simp only [ext, hz, ↓reduceDIte]
      exact measurable_const
  refine ⟨fun x => fun i : Fin M => stationaryHorizontalIncrement ρ (ext x) i n, ?_, ?_⟩
  · exact measurable_pi_iff.2 fun i =>
      (measurable_stationaryHorizontalIncrement ρ i n).comp hext
  · intro ω
    funext i
    refine stationaryHorizontalIncrement_eq_of_eqOn i.2 fun z h0 h1 => ?_
    have hz : z ∈ S := Finset.mem_Icc.2 ⟨h0, h1⟩
    simp [ext, hz]

/-! ## Laws of vectors of site weights -/

/-- The weights at an injective family of `k` sites are independent `Exp(1)` variables: their
joint law under the i.i.d. `Exp(1)` environment is the product measure. -/
theorem map_environment_siteVector {k : ℕ} {e : Fin k → Lattice} (he : Function.Injective e) :
    (environmentLaw (expMeasure 1)).map (fun ω : Environment => fun i : Fin k => ω (e i)) =
      Measure.pi fun _ : Fin k => expMeasure 1 := by
  have hind : iIndepFun (fun (i : Fin k) (ω : Environment) => ω (e i))
      (environmentLaw (expMeasure 1)) :=
    (iIndepFun_environment_eval (expMeasure 1)).precomp he
  have hlaw := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_environment_eval (e i)).aemeasurable)).1 hind
  simpa only [environmentLaw_map_eval] using hlaw

/-- The site `(j, n + 1)` of the row at height `n + 1`, for `j = 0, ..., M`. -/
private def rowSite (n M : ℕ) (j : Fin (M + 1)) : Lattice := (((j : ℕ) : ℤ), (n : ℤ) + 1)

private theorem rowSite_injective (n M : ℕ) : Function.Injective (rowSite n M) := by
  intro a b hab
  have h : (((a : ℕ) : ℤ)) = ((b : ℕ) : ℤ) := congrArg Prod.fst hab
  exact Fin.ext (by exact_mod_cast h)

private theorem rowSite_zero (n M : ℕ) : rowSite n M 0 = (0, (n : ℤ) + 1) := by
  simp [rowSite]

private theorem rowSite_succ (n M : ℕ) (i : Fin M) :
    rowSite n M i.succ = (((i : ℕ) : ℤ) + 1, (n : ℤ) + 1) := by
  simp [rowSite, Fin.val_succ]

/-- The pair (weight at `(0, n + 1)` divided by `ρ`, bulk weights at `(1, n + 1), ..., (M, n + 1)`)
has law `Exp(ρ)` times `Exp(1)^M`. The first coordinate is `Exp(1) / ρ`, which is `Exp(ρ)`, and the
`M + 1` weights are independent. -/
theorem map_boundaryBulk {ρ : ℝ} (hρ : 0 < ρ) (M n : ℕ) :
    (environmentLaw (expMeasure 1)).map
        (fun ω : Environment =>
          (ω (0, (n : ℤ) + 1) / ρ, fun i : Fin M => ω (((i : ℕ) : ℤ) + 1, (n : ℤ) + 1))) =
      (expMeasure ρ).prod (Measure.pi fun _ : Fin M => expMeasure 1) := by
  have hℓ := map_environment_siteVector (rowSite_injective n M)
  have hℓm : Measurable (fun ω : Environment => fun j : Fin (M + 1) => ω (rowSite n M j)) :=
    measurable_pi_iff.2 fun j => measurable_environment_eval _
  have hdiv : Measurable (fun t : ℝ => t / ρ) := measurable_id.div_const ρ
  have hΦ₁m : Measurable (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => ℝ) 0) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => ℝ) 0).measurable
  have hΦ₂m : Measurable (Prod.map (fun t : ℝ => t / ρ) (id : (Fin M → ℝ) → (Fin M → ℝ))) :=
    hdiv.prodMap measurable_id
  have hfun : (fun ω : Environment =>
        (ω (0, (n : ℤ) + 1) / ρ, fun i : Fin M => ω (((i : ℕ) : ℤ) + 1, (n : ℤ) + 1))) =
      Prod.map (fun t : ℝ => t / ρ) (id : (Fin M → ℝ) → (Fin M → ℝ)) ∘
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => ℝ) 0) ∘
          (fun ω : Environment => fun j : Fin (M + 1) => ω (rowSite n M j))) := by
    funext ω
    refine Prod.ext ?_ (funext fun i => ?_)
    · show ω (0, (n : ℤ) + 1) / ρ = ω (rowSite n M 0) / ρ
      rw [rowSite_zero]
    · show ω (((i : ℕ) : ℤ) + 1, (n : ℤ) + 1) = ω (rowSite n M i.succ)
      rw [rowSite_succ]
  have hsplit := (measurePreserving_piFinSuccAbove
    (α := fun _ : Fin (M + 1) => ℝ) (fun _ => expMeasure 1) 0).map_eq
  rw [hfun, ← Measure.map_map hΦ₂m (hΦ₁m.comp hℓm), ← Measure.map_map hΦ₁m hℓm, hℓ]
  rw [hsplit, ← Measure.map_prod_map _ _ hdiv measurable_id, Measure.map_id,
    expMeasure_one_map_div hρ]

/-- The weights at the `M + 1` sites `(0, n + 1), ..., (M, n + 1)` of the row at height `n + 1`
give a measurable observable: there is a finite set `T` of sites, all at height `n + 1`, and a
measurable function `g` of the weights on `T` whose value is the pair (weight at `(0, n + 1)`
divided by `ρ`, bulk weights at `(1, n + 1), ..., (M, n + 1)`). -/
theorem exists_measurable_boundaryBulk_observable (ρ : ℝ) (M n : ℕ) :
    ∃ (T : Finset Lattice) (g : ({z : Lattice // z ∈ T} → ℝ) → ℝ × (Fin M → ℝ)),
      Measurable g ∧ (∀ z ∈ T, z.2 = (n : ℤ) + 1) ∧ ∀ ω : Environment,
        (ω (0, (n : ℤ) + 1) / ρ, fun i : Fin M => ω (((i : ℕ) : ℤ) + 1, (n : ℤ) + 1)) =
          g (fun t => ω t.val) := by
  classical
  let T : Finset Lattice := Finset.univ.image (rowSite n M)
  have hmem : ∀ j : Fin (M + 1), rowSite n M j ∈ T := fun j =>
    Finset.mem_image_of_mem _ (Finset.mem_univ j)
  refine ⟨T, fun x => (x ⟨rowSite n M 0, hmem 0⟩ / ρ, fun i : Fin M => x ⟨rowSite n M i.succ,
    hmem i.succ⟩), ?_, ?_, ?_⟩
  · have hx0 : Measurable (fun x : {z : Lattice // z ∈ T} → ℝ => x ⟨rowSite n M 0, hmem 0⟩) :=
      measurable_pi_apply _
    exact (hx0.div_const ρ).prodMk (measurable_pi_iff.2 fun i => measurable_pi_apply _)
  · intro z hz
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
    rfl
  · intro ω
    refine Prod.ext ?_ (funext fun i => ?_)
    · show ω (0, (n : ℤ) + 1) / ρ = ω (rowSite n M 0) / ρ
      rw [rowSite_zero]
    · show ω (((i : ℕ) : ℤ) + 1, (n : ℤ) + 1) = ω (rowSite n M i.succ)
      rw [rowSite_succ]

end LPPDifferentiability
