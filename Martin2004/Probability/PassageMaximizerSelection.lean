/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.PassageMeasurable
public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.Animals.PathSets
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith

/-!
# Maximizing-path selection

Finite deterministic maximizing-path selection, including measurable ties and clipping.
The proof fixes an arbitrary injective finite path code to order ties. This order need not
be lexicographic; only its independence from the environment matters in Martin (2004),
Lemma 3.6. No chosen selector is installed as a public definition.
-/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Updating one actual site changes a path score once precisely when it is collected.
The collected-site sum uses injectivity of the actual path vertices. -/
theorem pathWeight_update (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (v : Lattice) (t : ℝ) :
    pathWeight (Function.update ω v t) p =
      pathWeight ω p + if v ∈ p.collectedSites then t - ω v else 0 := by
  classical
  rw [p.pathWeight_eq_sum_collectedSites, p.pathWeight_eq_sum_collectedSites]
  by_cases hv : v ∈ p.collectedSites
  · rw [ite_eq_left hv, Finset.sum_update_of_mem hv, Finset.sdiff_singleton_eq_erase]
    have hsum := Finset.sum_erase_add p.collectedSites ω hv
    linarith only [hsum]
  · rw [ite_eq_right hv, Finset.sum_update_of_notMem hv, add_zero]

private theorem exists_least_maximizer {α : Type*} [Fintype α] [Nonempty α]
    (score : α → ℝ) (code : α → ℕ) :
    ∃ p, ∀ q, score q ≤ score p ∧ (score q = score p → code p ≤ code q) := by
  classical
  obtain ⟨p₀, _, hp₀⟩ := Finset.exists_max_image Finset.univ score Finset.univ_nonempty
  let s := Finset.univ.filter fun p => score p = score p₀
  have hs : s.Nonempty := ⟨p₀, by simp [s]⟩
  obtain ⟨p, hp, hleast⟩ := Finset.exists_min_image s code hs
  have hscore : score p = score p₀ := (Finset.mem_filter.mp hp).2
  refine ⟨p, fun q => ⟨?_, ?_⟩⟩
  · rw [hscore]
    exact hp₀ q (Finset.mem_univ q)
  · intro hq
    apply hleast q
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq.trans hscore⟩

private theorem least_maximizer_unique {α : Type*} (score : α → ℝ)
    (code : α → ℕ) (hinj : Function.Injective code) {p q : α}
    (hp : ∀ r, score r ≤ score p ∧ (score r = score p → code p ≤ code r))
    (hq : ∀ r, score r ≤ score q ∧ (score r = score q → code q ≤ code r)) : p = q := by
  have heq : score q = score p := le_antisymm (hp q).1 (hq p).1
  exact hinj (le_antisymm ((hp q).2 heq) ((hq p).2 heq.symm))

/-- A measurable deterministic maximizer exists, with single-site membership monotonicity.
All three properties concern the same selector. Its fibers are measurable directly,
without any measurable-space instance on the path type. -/
theorem exists_measurable_maximizing_path_selector (u : Lattice) (d : ℕ × ℕ) :
    ∃ σ : Environment → Path u d,
      (∀ p, MeasurableSet {ω | σ ω = p}) ∧
      (∀ ω, pathWeight ω (σ ω) = lastPassage ω u d) ∧
      (∀ v ω, Monotone (fun t : ℝ =>
        if v ∈ (σ (Function.update ω v t)).collectedSites then (1 : ℝ) else 0)) := by
  classical
  let code : Path u d → ℕ := fun p => (Fintype.equivFin (Path u d) p).val
  have hinj : Function.Injective code :=
    Fin.val_injective.comp (Fintype.equivFin (Path u d)).injective
  choose σ hσ using fun ω : Environment =>
    exists_least_maximizer (pathWeight ω : Path u d → ℝ) code
  have hmax (ω : Environment) : pathWeight ω (σ ω) = lastPassage ω u d := by
    obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u d
    exact le_antisymm (pathWeight_le_lastPassage ω (σ ω)) (hp ▸ (hσ ω p).1)
  refine ⟨σ, ?_, hmax, ?_⟩
  · intro p
    have hfiber : {ω | σ ω = p} =
        ⋂ q : Path u d, {ω | pathWeight ω q ≤ pathWeight ω p ∧
          (pathWeight ω q = pathWeight ω p → code p ≤ code q)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro heq
        simpa only [heq] using hσ ω
      · intro hp
        exact least_maximizer_unique (pathWeight ω) code hinj (hσ ω) hp
    rw [hfiber]
    apply MeasurableSet.iInter
    intro q
    have hle := measurableSet_le (measurable_pathWeight q) (measurable_pathWeight p)
    have heq := measurableSet_eq_fun (measurable_pathWeight q) (measurable_pathWeight p)
    by_cases hc : code p ≤ code q
    · simpa only [hc, implies_true, and_true] using hle
    · convert hle.inter heq.compl using 1
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, hc, imp_false]
  · intro v ω t t' htt'
    by_cases ht : t = t'
    · subst t'
      exact le_refl _
    have hlt : t < t' := lt_of_le_of_ne htt' ht
    by_cases hv : v ∈ (σ (Function.update ω v t)).collectedSites
    · have hv' : v ∈ (σ (Function.update ω v t')).collectedSites := by
        by_contra hn
        have hold := (hσ (Function.update ω v t)
          (σ (Function.update ω v t'))).1
        have hnew := (hσ (Function.update ω v t')
          (σ (Function.update ω v t))).1
        rw [pathWeight_update, pathWeight_update, ite_eq_right hn, ite_eq_left hv] at hold
        rw [pathWeight_update, pathWeight_update, ite_eq_left hv, ite_eq_right hn] at hnew
        linarith only [hold, hnew, hlt]
      simp only [ite_eq_left hv, ite_eq_left hv', le_refl]
    · simp only [ite_eq_right hv]
      split_ifs <;> norm_num

/-- Composition with clipping preserves measurability, maximization and monotone
membership in the original weight. Equal clipped fields give the same path. -/
theorem exists_measurable_clipped_maximizing_path_selector
    (u : Lattice) (d : ℕ × ℕ) (L : ℝ) :
    ∃ σ : Environment → Path u d,
      (∀ p, MeasurableSet {ω | σ ω = p}) ∧
      (∀ ω, pathWeight (fun z => max (-L) (min L (ω z))) (σ ω) =
        lastPassage (fun z => max (-L) (min L (ω z))) u d) ∧
      (∀ v ω, Monotone (fun t : ℝ =>
        if v ∈ (σ (Function.update ω v t)).collectedSites then (1 : ℝ) else 0)) ∧
      (∀ ω ω', (∀ z, max (-L) (min L (ω z)) = max (-L) (min L (ω' z))) →
        σ ω = σ ω') := by
  classical
  obtain ⟨τ, hfiber, hmax, hmono⟩ := exists_measurable_maximizing_path_selector u d
  let clip : Environment → Environment := fun ω z => max (-L) (min L (ω z))
  have hclip : Measurable clip := Measurable.of_eval fun z =>
    measurable_const.max (measurable_const.min (measurable_pi_apply z))
  have hupdate (ω : Environment) (v : Lattice) (t : ℝ) :
      clip (Function.update ω v t) = Function.update (clip ω) v (max (-L) (min L t)) := by
    funext z
    by_cases hz : z = v
    · subst z
      simp only [clip, Function.update_self]
    · simp only [clip, Function.update_of_ne hz]
  refine ⟨fun ω => τ (clip ω), ?_, fun ω => hmax (clip ω), ?_, ?_⟩
  · intro p
    exact hclip (hfiber p)
  · intro v ω t t' htt'
    dsimp only
    simp only [hupdate]
    exact hmono v (clip ω) (max_le_max_left _ (min_le_min_left _ htt'))
  · intro ω ω' heq
    exact congrArg τ (funext heq)

end LPPDifferentiability
