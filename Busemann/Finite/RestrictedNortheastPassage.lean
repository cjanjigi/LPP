/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Busemann.Process.NortheastBoundaryPotential
public import LPP_Foundations.Model.Paths.Swap
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
import LPP_Foundations.Model.Paths.FirstTopRow
import LPP_Foundations.Model.Paths.PrefixLocality
import Busemann.Process.NorthBoundaryTail
import LPP_Foundations.Model.LastPassage.Swap
import Mathlib.Tactic

/-! # Finite last-step restrictions of the northeast boundary passage

The objects here use both boundary fields in GRS arXiv:1510.00859v2 (6.8).
The selected final step is required to be reachable, so the real maximum
never represents an empty class.
-/

@[expose] public section

open LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

/-- Each positive selected coordinate admits a path with that last step.
This supplies the nonempty restricted classes preceding GRS (6.9)–(6.10). -/
theorem restrictedNE_reachable (x : Lattice) (d : ℕ × ℕ) (i : Fin 2)
    (hi : if i = 0 then 0 < d.1 else 0 < d.2) :
    ∃ p : LPPDifferentiability.Path x d, ∃ k : Fin (d.1 + d.2),
      k.val + 1 = d.1 + d.2 ∧
      p.vertex k.castSucc = x + ((d.1 : ℤ), (d.2 : ℤ)) - finiteEdgeStep i := by
  fin_cases i
  · have hd : 0 < d.1 := hi
    let k : Fin (d.1 + d.2) := ⟨d.1 + d.2 - 1, by omega⟩
    refine ⟨(horizontalFirst x.swap d.swap).swap, k, by dsimp [k]; omega, ?_⟩
    apply Prod.ext <;> simp [LPPDifferentiability.Path.swap, horizontalFirst,
      k, finiteEdgeStep, Prod.swap] <;> omega
  · have hd : 0 < d.2 := hi
    let k : Fin (d.1 + d.2) := ⟨d.1 + d.2 - 1, by omega⟩
    refine ⟨horizontalFirst x d, k, by dsimp [k]; omega, ?_⟩
    apply Prod.ext <;> simp [horizontalFirst, k, finiteEdgeStep] <;> omega

/-- The literal maximum in GRS (6.8) restricted to the chosen final predecessor.
Its proof argument excludes unreachable, empty classes. -/
noncomputable def restrictedNE (ω : Environment) (C : Lattice → Lattice → ℝ)
    (x : Lattice) (d : ℕ × ℕ) (i : Fin 2)
    (hi : if i = 0 then 0 < d.1 else 0 < d.2) : ℝ :=
  let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
  let ωNE : Environment := fun z =>
    if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0))
    else if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
  have _hreach := restrictedNE_reachable x d i hi
  sSup {r : ℝ | ∃ p : LPPDifferentiability.Path x d,
    (∃ k : Fin (d.1 + d.2), k.val + 1 = d.1 + d.2 ∧
      p.vertex k.castSucc = v - finiteEdgeStep i) ∧ pathWeight ωNE p = r}

private def neEnv (ω : Environment) (C : Lattice → Lattice → ℝ) (v : Lattice) :
    Environment := fun z =>
  if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0))
  else if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z

private def lastClass {x : Lattice} {d : ℕ × ℕ}
    (p : LPPDifferentiability.Path x d) (i : Fin 2) : Prop :=
  ∃ k : Fin (d.1 + d.2), k.val + 1 = d.1 + d.2 ∧
    p.vertex k.castSucc = x + ((d.1 : ℤ), (d.2 : ℤ)) - finiteEdgeStep i

private def classValues (ω : Environment) (C : Lattice → Lattice → ℝ)
    (x : Lattice) (d : ℕ × ℕ) (i : Fin 2) : Set ℝ :=
  {r | ∃ p : LPPDifferentiability.Path x d, lastClass p i ∧
    pathWeight (neEnv ω C (x + ((d.1 : ℤ), (d.2 : ℤ)))) p = r}

private theorem classValues_finite (ω : Environment) (C : Lattice → Lattice → ℝ)
    (x : Lattice) (d : ℕ × ℕ) (i : Fin 2) : (classValues ω C x d i).Finite := by
  apply (Set.finite_range (pathWeight
    (neEnv ω C (x + ((d.1 : ℤ), (d.2 : ℤ)))) :
      LPPDifferentiability.Path x d → ℝ)).subset
  rintro r ⟨p, _, rfl⟩
  exact ⟨p, rfl⟩

private theorem classValues_nonempty (ω : Environment) (C : Lattice → Lattice → ℝ)
    (x : Lattice) (d : ℕ × ℕ) (i : Fin 2)
    (hi : if i = 0 then 0 < d.1 else 0 < d.2) :
    (classValues ω C x d i).Nonempty := by
  obtain ⟨p, hp⟩ := restrictedNE_reachable x d i hi
  exact ⟨_, p, hp, rfl⟩

private theorem pathWeight_le_restrictedNE (ω : Environment)
    (C : Lattice → Lattice → ℝ) {x : Lattice} {d : ℕ × ℕ}
    (i : Fin 2) (hi : if i = 0 then 0 < d.1 else 0 < d.2)
    (p : LPPDifferentiability.Path x d) (hp : lastClass p i) :
    pathWeight (neEnv ω C (x + ((d.1 : ℤ), (d.2 : ℤ)))) p ≤
      restrictedNE ω C x d i hi := by
  exact le_csSup (classValues_finite ω C x d i).bddAbove ⟨p, hp, rfl⟩

private theorem restrictedNE_le (ω : Environment) (C : Lattice → Lattice → ℝ)
    (x : Lattice) (d : ℕ × ℕ) (i : Fin 2)
    (hi : if i = 0 then 0 < d.1 else 0 < d.2) (a : ℝ)
    (h : ∀ p : LPPDifferentiability.Path x d, lastClass p i →
      pathWeight (neEnv ω C (x + ((d.1 : ℤ), (d.2 : ℤ)))) p ≤ a) :
    restrictedNE ω C x d i hi ≤ a := by
  apply csSup_le (classValues_nonempty ω C x d i hi)
  rintro r ⟨p, hp, rfl⟩
  exact h p hp

private theorem lastClass_cases {x : Lattice} {d : ℕ × ℕ}
    (hpos : 0 < d.1 + d.2) (p : LPPDifferentiability.Path x d) :
    lastClass p 0 ∨ lastClass p 1 := by
  let k : Fin (d.1 + d.2) := ⟨d.1 + d.2 - 1, by omega⟩
  have hlast : k.succ = Fin.last (d.1 + d.2) := by
    apply Fin.ext
    dsimp [k]
    omega
  have hfinish : p.vertex k.succ = x + ((d.1 : ℤ), (d.2 : ℤ)) := by
    rw [hlast, p.finish]
  rcases p.step k with hstep | hstep
  · left
    refine ⟨k, by dsimp [k]; omega, ?_⟩
    rw [hfinish] at hstep
    simpa only [finiteEdgeStep, Fin.val_zero, ite_true] using
      (eq_sub_iff_add_eq.mpr hstep.symm)
  · right
    refine ⟨k, by dsimp [k]; omega, ?_⟩
    rw [hfinish] at hstep
    simpa only [finiteEdgeStep, Fin.val_one, one_ne_zero, ite_false] using
      (eq_sub_iff_add_eq.mpr hstep.symm)

private theorem class_zero_fst_lt {x : Lattice} {d : ℕ × ℕ}
    (p : LPPDifferentiability.Path x d) (hp : lastClass p 0)
    (j : Fin (d.1 + d.2)) :
    (p.vertex j.castSucc).1 < (x + ((d.1 : ℤ), (d.2 : ℤ))).1 := by
  obtain ⟨k, hk, hvertex⟩ := hp
  have hjk : j.castSucc ≤ k.castSucc := by
    change j.val ≤ k.val
    omega
  have hmono := p.fst_monotone hjk
  have hcoord := congrArg Prod.fst hvertex
  change (p.vertex j.castSucc).1 ≤ (p.vertex k.castSucc).1 at hmono
  change (p.vertex k.castSucc).1 = (x + ((d.1 : ℤ), (d.2 : ℤ))).1 - 1 at hcoord
  omega

private theorem class_one_snd_lt {x : Lattice} {d : ℕ × ℕ}
    (p : LPPDifferentiability.Path x d) (hp : lastClass p 1)
    (j : Fin (d.1 + d.2)) :
    (p.vertex j.castSucc).2 < (x + ((d.1 : ℤ), (d.2 : ℤ))).2 := by
  obtain ⟨k, hk, hvertex⟩ := hp
  have hjk : j.castSucc ≤ k.castSucc := by
    change j.val ≤ k.val
    omega
  have hmono := p.snd_monotone hjk
  have hcoord := congrArg Prod.snd hvertex
  change (p.vertex j.castSucc).2 ≤ (p.vertex k.castSucc).2 at hmono
  change (p.vertex k.castSucc).2 = (x + ((d.1 : ℤ), (d.2 : ℤ))).2 - 1 at hcoord
  omega

/-- The maximum of the two final-step classes is the cocycle potential.
This is the finite recovery identity for GRS (6.8), before Lemma 6.4. -/
theorem restrictedNE_max_eq_cocycle (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (x : Lattice) (d : ℕ × ℕ) (hd1 : 0 < d.1) (hd2 : 0 < d.2) :
    max (restrictedNE ω C x d 0 (by simpa using hd1))
      (restrictedNE ω C x d 1 (by simpa using hd2)) = C x (x + ((d.1 : ℤ), (d.2 : ℤ))) := by
  let W := neEnv ω C (x + ((d.1 : ℤ), (d.2 : ℤ)))
  have hpotential : lastPassage W x d = C x (x + ((d.1 : ℤ), (d.2 : ℤ))) :=
    (northeast_boundary_potential_eq_cocycle ω C hC hrec x d).1
  rw [← hpotential]
  apply le_antisymm
  · apply max_le
    · exact restrictedNE_le ω C x d 0 (by simpa using hd1) _
        (fun p _ => pathWeight_le_lastPassage W p)
    · exact restrictedNE_le ω C x d 1 (by simpa using hd2) _
        (fun p _ => pathWeight_le_lastPassage W p)
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage W x d
    rw [← hp]
    rcases lastClass_cases (by omega) p with hzero | hone
    · exact (pathWeight_le_restrictedNE ω C 0 (by simpa using hd1) p hzero).trans
        (le_max_left _ _)
    · exact (pathWeight_le_restrictedNE ω C 1 (by simpa using hd2) p hone).trans
        (le_max_right _ _)

/-- At the same terminal point, a one-sided boundary value is bounded by its
restricted northeast class or the ordinary passage value. This is the finite
path partition used before the restricted limits in GRS Lemma 6.4 and JR
Theorem 4.16; it requires no cocycle or recovery assumption. -/
theorem one_sided_boundary_passage_le_max_restrictedNE
    (ω : Environment) (C : Lattice → Lattice → ℝ) (x : Lattice) (d : ℕ × ℕ)
    (hd1 : 0 < d.1) (hd2 : 0 < d.2) :
    let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
    let N : Environment := fun z =>
      if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
    let E : Environment := fun z =>
      if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
    lastPassage N x d ≤ max (restrictedNE ω C x d 0 (by simpa using hd1))
      (lastPassage ω x d) ∧
    lastPassage E x d ≤ max (restrictedNE ω C x d 1 (by simpa using hd2))
      (lastPassage ω x d) := by
  let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
  let N : Environment := fun z =>
    if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
  let E : Environment := fun z =>
    if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z
  constructor
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage N x d
    rw [← hp]
    rcases lastClass_cases (by omega) p with hzero | hone
    · have hweight : pathWeight N p = pathWeight (neEnv ω C v) p := by
        unfold pathWeight
        apply Finset.sum_congr rfl
        intro j _
        have hleft : (p.vertex j.castSucc).1 ≠ v.1 :=
          ne_of_lt (class_zero_fst_lt p hzero j)
        simp only [N, neEnv, hleft, false_and, ite_false]
      rw [hweight]
      exact (pathWeight_le_restrictedNE ω C 0 (by simpa using hd1) p hzero).trans
        (le_max_left _ _)
    · have hweight : pathWeight N p = pathWeight ω p := by
        unfold pathWeight
        apply Finset.sum_congr rfl
        intro j _
        have hbelow : (p.vertex j.castSucc).2 ≠ v.2 :=
          ne_of_lt (class_one_snd_lt p hone j)
        simp only [N, hbelow, false_and, ite_false]
      rw [hweight]
      exact (pathWeight_le_lastPassage ω p).trans (le_max_right _ _)
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage E x d
    rw [← hp]
    rcases lastClass_cases (by omega) p with hzero | hone
    · have hweight : pathWeight E p = pathWeight ω p := by
        unfold pathWeight
        apply Finset.sum_congr rfl
        intro j _
        have hleft : (p.vertex j.castSucc).1 ≠ v.1 :=
          ne_of_lt (class_zero_fst_lt p hzero j)
        simp only [E, hleft, false_and, ite_false]
      rw [hweight]
      exact (pathWeight_le_lastPassage ω p).trans (le_max_right _ _)
    · have hweight : pathWeight E p = pathWeight (neEnv ω C v) p := by
        unfold pathWeight
        apply Finset.sum_congr rfl
        intro j _
        have hbelow : (p.vertex j.castSucc).2 ≠ v.2 :=
          ne_of_lt (class_one_snd_lt p hone j)
        simp only [E, neEnv, hbelow, false_and, ite_false]
      rw [hweight]
      exact (pathWeight_le_restrictedNE ω C 1 (by simpa using hd2) p hone).trans
        (le_max_left _ _)

private theorem prefix_step (ω : Environment) {x : Lattice} {d : ℕ × ℕ}
    (p : LPPDifferentiability.Path x d) (t : Fin (d.1 + d.2)) :
    pathWeight ω (p.prefixPath t.succ) =
      pathWeight ω (p.prefixPath t.castSucc) + ω (p.vertex t.castSucc) := by
  have hleft := p.splitDisplacement_length t.castSucc
  have hright := p.splitDisplacement_length t.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at hleft hright
  unfold pathWeight
  rw [← Fin.sum_congr' _ hright.symm, ← Fin.sum_congr' _ hleft.symm]
  rw [Fin.sum_univ_castSucc]
  rfl

private theorem north_class_le_exit (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (x : Lattice) (d : ℕ × ℕ)
    (hd1 : 0 < d.1) (hd2 : 0 < d.2) :
    restrictedNE ω C x d 0 (by simpa using hd1) ≤
      (Finset.Icc 1 d.1).sup' (Finset.nonempty_Icc.mpr hd1)
        (fun ℓ => lastPassage ω x (d.1 - ℓ, d.2 - 1) +
          ω (x + ((d.1 : ℤ), (d.2 : ℤ)) - ((ℓ : ℤ), 1)) +
          C (x + ((d.1 : ℤ), (d.2 : ℤ)) - ((ℓ : ℤ), 0))
            (x + ((d.1 : ℤ), (d.2 : ℤ)))) := by
  let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
  let W := neEnv ω C v
  apply restrictedNE_le ω C x d 0 (by simpa using hd1)
  intro p hp
  -- Split immediately before the first top-row entry, as in GRS Lemma 6.4.
  obtain ⟨j, hjTop, hjBefore, hjHeight⟩ := p.exists_first_top_row_vertex
  have hjpos : 0 < j.val := by
    by_contra h
    have hjzero : j = 0 := by apply Fin.ext; change j.val = 0; omega
    rw [hjzero, p.start] at hjTop
    omega
  let t : Fin (d.1 + d.2) := ⟨j.val - 1, by omega⟩
  have htj : t.succ = j := by apply Fin.ext; dsimp [t]; omega
  have htBefore : t.castSucc < j := by change t.val < j.val; dsimp [t]; omega
  have htBelow := hjBefore t.castSucc htBefore
  have hentry : p.vertex j = p.vertex t.castSucc + (0, 1) := by
    rcases p.step t with hh | hv
    · rw [htj] at hh
      have hs := congrArg Prod.snd hh
      simp only [Prod.snd_add] at hs
      omega
    · rwa [htj] at hv
  let e := p.splitDisplacement t.castSucc
  let ℓ := d.1 - e.1
  have heLe := p.splitDisplacement_le t.castSucc
  have heFirstLe : e.1 ≤ d.1 := heLe.1
  have he1 := p.splitDisplacement_fst_cast t.castSucc
  have he2 := p.splitDisplacement_snd_cast t.castSucc
  have hleft := class_zero_fst_lt p hp t
  have hentry2 := congrArg Prod.snd hentry
  change (p.vertex j).2 = (p.vertex t.castSucc).2 + 1 at hentry2
  have hell : ℓ ∈ Finset.Icc 1 d.1 := by
    simp only [Finset.mem_Icc]
    dsimp [ℓ, e]
    simp only [Prod.fst_add] at hleft
    omega
  have he : e = (d.1 - ℓ, d.2 - 1) := by
    apply Prod.ext
    · dsimp only [ℓ]
      omega
    · dsimp only [e]
      omega
  have hentryVertex : p.vertex j = v - ((ℓ : ℤ), 0) := by
    have hentry1 := congrArg Prod.fst hentry
    apply Prod.ext <;> simp only [v, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub] <;> dsimp [ℓ, e] at * <;> omega
  have hpred : p.vertex t.castSucc = v - ((ℓ : ℤ), 1) := by
    rw [hentryVertex] at hentry
    apply Prod.ext <;> have hc := congrArg Prod.fst hentry <;>
      have hc2 := congrArg Prod.snd hentry <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at * <;> omega
  have hremaining : d - p.splitDisplacement j = (ℓ, 0) := by
    have hfirst := p.splitDisplacement_fst_cast j
    rw [hentryVertex] at hfirst
    apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;>
      dsimp [v, ℓ, e] at * <;> omega
  have hprefix : pathWeight W (p.prefixPath j) = pathWeight ω (p.prefixPath j) := by
    apply LPP.pathWeight_prefix_eq_of_eq_before
    intro a ha
    have hbelow := hjBefore a.castSucc (by change a.val < j.val; exact ha)
    have hnotNorth : (p.vertex a.castSucc).2 ≠ v.2 := ne_of_lt hbelow
    have hnotEast : (p.vertex a.castSucc).1 ≠ v.1 :=
      ne_of_lt (class_zero_fst_lt p hp a)
    simp only [W, neEnv, hnotNorth, hnotEast, false_and, ite_false]
  have htail : pathWeight W (p.suffix j) ≤ C (v - ((ℓ : ℤ), 0)) v := by
    calc
      _ ≤ lastPassage W (p.vertex j) (d - p.splitDisplacement j) :=
        pathWeight_le_lastPassage W (p.suffix j)
      _ = _ := by
        rw [hentryVertex, hremaining]
        exact north_boundary_horizontal_passage_eq_cocycle
          (fun z => if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z)
          C hC v ℓ
  have hbound : pathWeight W p ≤ lastPassage ω x (d.1 - ℓ, d.2 - 1) +
      ω (v - ((ℓ : ℤ), 1)) + C (v - ((ℓ : ℤ), 0)) v := by
    have hpreStep : pathWeight ω (p.prefixPath j) =
        pathWeight ω (p.prefixPath t.castSucc) + ω (p.vertex t.castSucc) := by
      rw [← htj]
      exact prefix_step ω p t
    rw [pathWeight_split W p j, hprefix, hpreStep, hpred]
    have hprefixBound := pathWeight_le_lastPassage ω (p.prefixPath t.castSucc)
    change pathWeight ω (p.prefixPath t.castSucc) ≤ lastPassage ω x e at hprefixBound
    rw [he] at hprefixBound
    exact add_le_add (add_le_add hprefixBound (le_refl _)) htail
  exact hbound.trans (Finset.le_sup' (fun ℓ =>
    lastPassage ω x (d.1 - ℓ, d.2 - 1) + ω (v - ((ℓ : ℤ), 1)) +
      C (v - ((ℓ : ℤ), 0)) v) hell)

private theorem cast_path_weight (W : Environment) {x : Lattice} {e d : ℕ × ℕ}
    (h : e = d) (p : LPPDifferentiability.Path x e) :
    pathWeight W (h ▸ p) = pathWeight W p := by cases h; rfl

private theorem cast_path_class {x : Lattice} {e d : ℕ × ℕ} (h : e = d)
    (p : LPPDifferentiability.Path x e) (i : Fin 2) :
    lastClass (h ▸ p) i ↔ lastClass p i := by cases h; rfl

private theorem exit_le_north_class (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (x : Lattice) (d : ℕ × ℕ)
    (hd1 : 0 < d.1) (hd2 : 0 < d.2) :
    (Finset.Icc 1 d.1).sup' (Finset.nonempty_Icc.mpr hd1)
        (fun ℓ => lastPassage ω x (d.1 - ℓ, d.2 - 1) +
          ω (x + ((d.1 : ℤ), (d.2 : ℤ)) - ((ℓ : ℤ), 1)) +
          C (x + ((d.1 : ℤ), (d.2 : ℤ)) - ((ℓ : ℤ), 0))
            (x + ((d.1 : ℤ), (d.2 : ℤ)))) ≤
      restrictedNE ω C x d 0 (by simpa using hd1) := by
  let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
  let W := neEnv ω C v
  apply Finset.sup'_le
  intro ℓ hell
  obtain ⟨hellpos, hellle⟩ := Finset.mem_Icc.mp hell
  let e : ℕ × ℕ := (d.1 - ℓ, d.2 - 1)
  let a : ℕ × ℕ := (0, 1)
  let b : ℕ × ℕ := (ℓ, 0)
  let y : Lattice := x + ((e.1 : ℤ), (e.2 : ℤ))
  have hdisp : e + (a + b) = d := by
    apply Prod.ext <;> dsimp [e, a, b] <;> omega
  have hy : y = v - ((ℓ : ℤ), 1) := by
    apply Prod.ext <;> dsimp [y, v, e] <;> omega
  have hentry : y + ((a.1 : ℤ), (a.2 : ℤ)) = v - ((ℓ : ℤ), 0) := by
    rw [hy]
    apply Prod.ext <;> dsimp [a] <;> omega
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω x e
  let q₁ := horizontalFirst y a
  let q₂ := horizontalFirst (y + ((a.1 : ℤ), (a.2 : ℤ))) b
  let raw := p.concat (q₁.concat q₂)
  let q : LPPDifferentiability.Path x d := hdisp ▸ raw
  -- The ordinary prefix lies strictly inside both changed boundaries.
  have hprefix : pathWeight W p = pathWeight ω p := by
    unfold pathWeight
    apply Finset.sum_congr rfl
    intro j _
    have hrect := (p.vertex_mem_Icc j.castSucc).2
    have hleft : (p.vertex j.castSucc).1 < v.1 := by
      have hc := hrect.1
      dsimp [e, v] at hc ⊢
      omega
    have hbelow : (p.vertex j.castSucc).2 < v.2 := by
      have hc := hrect.2
      dsimp [e, v] at hc ⊢
      omega
    simp only [W, neEnv, ne_of_lt hleft, ne_of_lt hbelow, false_and, ite_false]
  -- The entering edge collects precisely its bulk predecessor weight.
  have hjoin : pathWeight W q₁ = ω (v - ((ℓ : ℤ), 1)) := by
    have hleft : y.1 < v.1 := by rw [hy]; change v.1 - (ℓ : ℤ) < v.1; omega
    have hbelow : y.2 < v.2 := by rw [hy]; change v.2 - 1 < v.2; omega
    rw [pathWeight_vertical]
    simp only [Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, add_zero]
    change W y = _
    rw [← hy]
    simp only [W, neEnv, ne_of_lt hleft, ne_of_lt hbelow, false_and, ite_false]
  -- Every collected tail weight is the corresponding cocycle edge.
  have htail : pathWeight W q₂ = C (v - ((ℓ : ℤ), 0)) v := by
    rw [pathWeight_horizontal, ← lastPassage_horizontal, hentry]
    exact north_boundary_horizontal_passage_eq_cocycle
      (fun z => if z.1 = v.1 ∧ z.2 < v.2 then C z (z + (0, 1)) else ω z)
      C hC v ℓ
  have hraw : lastClass raw 0 := by
    let s : Fin (b.1 + b.2) := ⟨ℓ - 1, by dsimp [b]; omega⟩
    let k : Fin ((e + (a + b)).1 + (e + (a + b)).2) :=
      ⟨e.1 + e.2 + (a.1 + a.2 + s.val), by dsimp [a, b, s]; omega⟩
    refine ⟨k, by dsimp [k, a, b, s]; omega, ?_⟩
    change (p.concat (q₁.concat q₂)).vertex
      ⟨e.1 + e.2 + (a.1 + a.2 + s.castSucc.val), _⟩ = _
    rw [p.concat_vertex_right (q₁.concat q₂)
      ⟨a.1 + a.2 + s.castSucc.val, by dsimp [a, b, s]; omega⟩,
      q₁.concat_vertex_right q₂ s.castSucc, q₂.vertex_horizontal]
    have hend : x + (((e + (a + b)).1 : ℤ), ((e + (a + b)).2 : ℤ)) = v := by
      rw [hdisp]
    rw [hend]
    simp only [finiteEdgeStep, Fin.val_zero, ite_true]
    apply Prod.ext <;> dsimp [q₂, y, e, a, b, s, v] <;> omega
  have hclass : lastClass q 0 := (cast_path_class hdisp raw 0).mpr hraw
  have hweight : pathWeight W q = lastPassage ω x e +
      ω (v - ((ℓ : ℤ), 1)) + C (v - ((ℓ : ℤ), 0)) v := by
    rw [show pathWeight W q = pathWeight W raw from cast_path_weight W hdisp raw]
    rw [pathWeight_concat, pathWeight_concat, hprefix, hp, hjoin, htail]
    exact (add_assoc _ _ _).symm
  rw [← hweight]
  exact pathWeight_le_restrictedNE ω C 0 (by simpa using hd1) q hclass

private theorem lastClass_swap {x : Lattice} {d : ℕ × ℕ}
    (p : LPPDifferentiability.Path x d) (i j : Fin 2)
    (hstep : finiteEdgeStep j = (finiteEdgeStep i).swap) (hp : lastClass p i) :
    lastClass p.swap j := by
  obtain ⟨k, hk, hvertex⟩ := hp
  let kS : Fin (d.2 + d.1) := Fin.cast (Nat.add_comm d.1 d.2) k
  refine ⟨kS, by dsimp [kS]; omega, ?_⟩
  rw [LPPDifferentiability.Path.swap_vertex]
  have hindex : Fin.cast (congrArg Nat.succ (Nat.add_comm d.2 d.1)) kS.castSucc =
      k.castSucc := by apply Fin.ext; rfl
  rw [hindex, hstep]
  exact congrArg Prod.swap hvertex

private theorem neEnv_swap (ω : Environment) (C : Lattice → Lattice → ℝ)
    (v z : Lattice) :
    neEnv ω C v z.swap =
      neEnv (fun u => ω u.swap) (fun a b => C a.swap b.swap) v.swap z := by
  by_cases hn : z.1 = v.2 ∧ z.2 < v.1
  · simp [neEnv, Prod.swap, hn]
  · by_cases he : z.2 = v.1 ∧ z.1 < v.2
    · simp [neEnv, Prod.swap, he]
    · simp [neEnv, Prod.swap, hn, he]

private theorem restrictedNE_swap (ω : Environment) (C : Lattice → Lattice → ℝ)
    (x : Lattice) (d : ℕ × ℕ) (i j : Fin 2)
    (hstep : finiteEdgeStep j = (finiteEdgeStep i).swap)
    (hi : if i = 0 then 0 < d.1 else 0 < d.2)
    (hj : if j = 0 then 0 < d.2 else 0 < d.1) :
    restrictedNE ω C x d i hi = restrictedNE (fun z => ω z.swap)
      (fun a b => C a.swap b.swap) x.swap d.swap j hj := by
  let ωS : Environment := fun z => ω z.swap
  let CS : Lattice → Lattice → ℝ := fun a b => C a.swap b.swap
  let v := x + ((d.1 : ℤ), (d.2 : ℤ))
  have hfield (z : Lattice) : neEnv ω C v z.swap = neEnv ωS CS v.swap z :=
    neEnv_swap ω C v z
  have hback : finiteEdgeStep i = (finiteEdgeStep j).swap := by
    rw [hstep, Prod.swap_swap]
  change sSup (classValues ω C x d i) = sSup (classValues ωS CS x.swap d.swap j)
  congr 1
  ext r
  constructor
  · rintro ⟨p, hp, hw⟩
    refine ⟨p.swap, lastClass_swap p i j hstep hp, ?_⟩
    rw [pathWeight_swap]
    have hfields : (fun z => neEnv ωS CS v.swap z.swap) = neEnv ω C v := by
      funext z
      exact (hfield z.swap).symm
    change pathWeight (fun z => neEnv ωS CS v.swap z.swap) p = r
    rw [hfields]
    exact hw
  · rintro ⟨p, hp, hw⟩
    refine ⟨p.swap, lastClass_swap p j i hback hp, ?_⟩
    rw [pathWeight_swap]
    change pathWeight (fun z => neEnv ω C v z.swap) p = r
    simp only [hfield]
    exact hw

/-- First entry into the north row or east column gives the exact restricted
maximum, including the ordinary predecessor weight. This is the finite
identity in the proof of GRS Lemma 6.4, (6.9)–(6.10). -/
theorem restrictedNE_eq_exitMax (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (x : Lattice) (d : ℕ × ℕ)
    (hd1 : 0 < d.1) (hd2 : 0 < d.2) :
    let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
    restrictedNE ω C x d 0 (by simpa using hd1) =
      (Finset.Icc 1 d.1).sup' (Finset.nonempty_Icc.mpr hd1)
        (fun ℓ => lastPassage ω x (d.1 - ℓ, d.2 - 1) +
          ω (v - ((ℓ : ℤ), 1)) + C (v - ((ℓ : ℤ), 0)) v) ∧
    restrictedNE ω C x d 1 (by simpa using hd2) =
      (Finset.Icc 1 d.2).sup' (Finset.nonempty_Icc.mpr hd2)
        (fun ℓ => lastPassage ω x (d.1 - 1, d.2 - ℓ) +
          ω (v - (1, (ℓ : ℤ))) + C (v - (0, (ℓ : ℤ))) v) := by
  constructor
  · exact le_antisymm (north_class_le_exit ω C hC x d hd1 hd2)
      (exit_le_north_class ω C hC x d hd1 hd2)
  · let ωS : Environment := fun z => ω z.swap
    let CS : Lattice → Lattice → ℝ := fun a b => C a.swap b.swap
    let v : Lattice := x + ((d.1 : ℤ), (d.2 : ℤ))
    have hCS : is_additive CS := fun a b c => hC a.swap b.swap c.swap
    have hnorth := le_antisymm (north_class_le_exit ωS CS hCS x.swap d.swap hd2 hd1)
      (exit_le_north_class ωS CS hCS x.swap d.swap hd2 hd1)
    have hswap := restrictedNE_swap ω C x d 1 0
      (by simp [finiteEdgeStep]) (by simpa using hd2) (by simpa using hd2)
    rw [← hswap] at hnorth
    have hobjective (ℓ : ℕ) :
        lastPassage ωS x.swap (d.2 - ℓ, d.1 - 1) +
          ωS (v.swap - ((ℓ : ℤ), 1)) + CS (v.swap - ((ℓ : ℤ), 0)) v.swap =
        lastPassage ω x (d.1 - 1, d.2 - ℓ) +
          ω (v - (1, (ℓ : ℤ))) + C (v - (0, (ℓ : ℤ))) v := by
      have hpassage : lastPassage ωS x.swap (d.2 - ℓ, d.1 - 1) =
          lastPassage ω x (d.1 - 1, d.2 - ℓ) :=
        (lastPassage_swap ω x.swap (d.2 - ℓ, d.1 - 1)).symm
      rw [hpassage]
      rfl
    change restrictedNE ω C x d 1 (by simpa using hd2) =
      (Finset.Icc 1 d.2).sup' (Finset.nonempty_Icc.mpr hd2)
        (fun ℓ => lastPassage ωS x.swap (d.2 - ℓ, d.1 - 1) +
          ωS (v.swap - ((ℓ : ℤ), 1)) + CS (v.swap - ((ℓ : ℤ), 0)) v.swap) at hnorth
    simpa only [hobjective] using hnorth

end LPP.Busemann
