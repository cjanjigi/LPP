/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPathBoundary
public import Busemann.Process.RightmostPathSeparation
public import Busemann.Process.RightmostPaths
import LPP_Foundations.Model.Paths.BoundaryHit
import LPP_Foundations.Model.LastPassage.Bounds
import LPP_Foundations.Model.RecoveryAntidiagonal
import Mathlib.Tactic

/-! Finite comparison for rightmost paths under a lowering of the environment. -/

@[expose] public section
open LPPDifferentiability LPP.Busemann
open scoped BigOperators

namespace LPP.Busemann

-- Recovery bounds the weight of every finite path by its endpoint potential.
private theorem path_weight_le_potential
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hr : recovers_environment ω C)
    {x : Lattice} {d : ℕ × ℕ} (p : LPPDifferentiability.Path x d) :
    pathWeight ω p ≤ C x (x + ((d.1 : ℤ), (d.2 : ℤ))) := by
  calc
    pathWeight ω p ≤ lastPassage ω x d := pathWeight_le_lastPassage ω p
    _ ≤ C x (x + ((d.1 : ℤ), (d.2 : ℤ))) :=
      (LPP.lastPassage_antidiagonal_comparison_and_attainment
        ω C hC hr x (d.1 + d.2)).1 d rfl

-- An actual old prefix with unchanged collected weights supplies one direction.
private theorem old_potential_le_new_of_unchanged_prefix
    (ω ω' : Environment) (C C' : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hC' : is_additive C')
    (hr : recovers_environment ω C) (hr' : recovers_environment ω' C')
    (x : Lattice) (N : ℕ)
    (hsame : ∀ j, j < N → ω' (rightmostCocyclePath C x j) =
      ω (rightmostCocyclePath C x j)) :
    C x (rightmostCocyclePath C x N) ≤ C' x (rightmostCocyclePath C x N) := by
  obtain ⟨p, htrace, hweight, _⟩ := exists_rightmostCocyclePath_prefix ω C hC hr x N
  have hlen : p.1.val + (N - p.1.val) = N := by
    have := p.1.isLt
    omega
  have hterminal : x + ((p.1.val : ℤ), ((N - p.1.val : ℕ) : ℤ)) =
      rightmostCocyclePath C x N := by
    have ht := htrace N (by omega)
    have hi : (⟨N, by omega⟩ : Fin (p.1.val + (N - p.1.val) + 1)) =
        Fin.last (p.1.val + (N - p.1.val)) := by
      apply Fin.ext
      simp only [Fin.val_last]
      exact hlen.symm
    rw [hi, p.2.finish] at ht
    exact ht
  have heq : pathWeight ω' p.2 = pathWeight ω p.2 := by
    unfold pathWeight
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.val < N := by have := i.isLt; omega
    have ht := htrace i.val (by omega)
    have hid : (⟨i.val, by omega⟩ : Fin (p.1.val + (N - p.1.val) + 1)) =
        i.castSucc := by apply Fin.ext; rfl
    rw [hid] at ht
    rw [ht]
    exact hsame i.val hi
  calc
    C x (rightmostCocyclePath C x N) = pathWeight ω p.2 := hweight.symm
    _ = pathWeight ω' p.2 := heq.symm
    _ ≤ C' x (x + ((p.1.val : ℤ), ((N - p.1.val : ℕ) : ℤ))) :=
      path_weight_le_potential ω' C' hC' hr' p.2
    _ = C' x (rightmostCocyclePath C x N) := by rw [hterminal]

-- An actual new prefix and lowering supply the reverse direction at its endpoint.
private theorem new_potential_le_old_of_lowering
    (ω ω' : Environment) (C C' : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hC' : is_additive C')
    (hr : recovers_environment ω C) (hr' : recovers_environment ω' C')
    (hLower : ∀ z, ω' z ≤ ω z) (x : Lattice) (N : ℕ) :
    C' x (rightmostCocyclePath C' x N) ≤ C x (rightmostCocyclePath C' x N) := by
  obtain ⟨p, htrace, hweight, _⟩ := exists_rightmostCocyclePath_prefix ω' C' hC' hr' x N
  have hlen : p.1.val + (N - p.1.val) = N := by
    have := p.1.isLt
    omega
  have hterminal : x + ((p.1.val : ℤ), ((N - p.1.val : ℕ) : ℤ)) =
      rightmostCocyclePath C' x N := by
    have ht := htrace N (by omega)
    have hi : (⟨N, by omega⟩ : Fin (p.1.val + (N - p.1.val) + 1)) =
        Fin.last (p.1.val + (N - p.1.val)) := by
      apply Fin.ext
      simp only [Fin.val_last]
      exact hlen.symm
    rw [hi, p.2.finish] at ht
    exact ht
  calc
    C' x (rightmostCocyclePath C' x N) = pathWeight ω' p.2 := hweight.symm
    _ ≤ pathWeight ω p.2 := pathWeight_mono ω' ω p.2 hLower
    _ ≤ C x (x + ((p.1.val : ℤ), ((N - p.1.val : ℕ) : ℤ))) :=
      path_weight_le_potential ω C hC hr p.2
    _ = C x (rightmostCocyclePath C' x N) := by rw [hterminal]

-- Additivity combines those two directions with boundary increment agreement.
private theorem equal_potentials_of_boundary_comparison
    (C C' : Lattice → Lattice → ℝ) (hC : is_additive C) (hC' : is_additive C')
    (x y z : Lattice) (hold : C x z ≤ C' x z) (hnew : C' x y ≤ C x y)
    (hboundary : C' y z = C y z) :
    C x z = C' x z ∧ C x y = C' x y := by
  have hc := hC x y z
  have hc' := hC' x y z
  constructor <;> linarith

-- Equal totals calibrate the first edge in the comparison environment.
private theorem first_edge_calibrated_of_total_comparison
    (ω η : Environment) (C D : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hD : is_additive D)
    (hr : recovers_environment ω C) (hs : recovers_environment η D)
    (x : Lattice) (N : ℕ) (hN : 0 < N)
    (hle : ∀ j, j < N → η (rightmostCocyclePath D x j) ≤
      ω (rightmostCocyclePath D x j))
    (heq : D x (rightmostCocyclePath D x N) =
      C x (rightmostCocyclePath D x N)) :
    C x (rightmostCocycleSuccessor D x) = ω x := by
  obtain ⟨p, htrace, hweight, _⟩ := exists_rightmostCocyclePath_prefix η D hD hs x N
  have hlen : p.1.val + (N - p.1.val) = N := by
    have := p.1.isLt
    omega
  have hterminal : x + ((p.1.val : ℤ), ((N - p.1.val : ℕ) : ℤ)) =
      rightmostCocyclePath D x N := by
    have ht := htrace N (by omega)
    have hi : (⟨N, by omega⟩ : Fin (p.1.val + (N - p.1.val) + 1)) =
        Fin.last (p.1.val + (N - p.1.val)) := by
      apply Fin.ext
      simp only [Fin.val_last]
      exact hlen.symm
    rw [hi, p.2.finish] at ht
    exact ht
  have hweightle : pathWeight η p.2 ≤ pathWeight ω p.2 := by
    unfold pathWeight
    apply Finset.sum_le_sum
    intro i _
    have hi : i.val < N := by have := i.isLt; omega
    have ht := htrace i.val (by omega)
    have hid : (⟨i.val, by omega⟩ : Fin (p.1.val + (N - p.1.val) + 1)) =
        i.castSucc := by apply Fin.ext; rfl
    rw [hid] at ht
    rw [ht]
    exact hle i.val hi
  have htotal : pathWeight ω p.2 =
      C x (x + ((p.1.val : ℤ), ((N - p.1.val : ℕ) : ℤ))) := by
    apply le_antisymm (path_weight_le_potential ω C hC hr p.2)
    calc
      C x (x + ((p.1.val : ℤ), ((N - p.1.val : ℕ) : ℤ))) =
          D x (rightmostCocyclePath D x N) := by rw [hterminal, heq]
      _ = pathWeight η p.2 := hweight.symm
      _ ≤ pathWeight ω p.2 := hweightle
  have hcal := (pathWeight_eq_cocycle_iff_calibrated ω C hC hr x
    (p.1.val, N - p.1.val) p.2).mp htotal
  have hfirst := hcal ⟨0, by omega⟩
  have hzero := htrace 0 (by omega)
  have hone := htrace 1 (by omega)
  have hzindex : (⟨0, by omega⟩ : Fin (p.1.val + (N - p.1.val) + 1)) =
      (⟨0, by omega⟩ : Fin (p.1.val + (N - p.1.val))).castSucc := by
    apply Fin.ext; rfl
  have hoindex : (⟨1, by omega⟩ : Fin (p.1.val + (N - p.1.val) + 1)) =
      (⟨0, by omega⟩ : Fin (p.1.val + (N - p.1.val))).succ := by
    apply Fin.ext; rfl
  rw [hzindex] at hzero
  rw [hoindex] at hone
  rw [hzero, hone] at hfirst
  simpa [rightmostCocyclePath] using hfirst

-- The equal boundary increment forces both first edges to cross-calibrate.
private theorem first_edges_cross_calibrated
    (ω ω' : Environment) (C C' : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hC' : is_additive C')
    (hr : recovers_environment ω C) (hr' : recovers_environment ω' C')
    (hLower : ∀ z, ω' z ≤ ω z) (x : Lattice) (K k : ℕ)
    (hK : 0 < K) (hk : 0 < k)
    (hsame : ∀ j, j < K → ω' (rightmostCocyclePath C x j) =
      ω (rightmostCocyclePath C x j))
    (hboundary : C' (rightmostCocyclePath C' x k) (rightmostCocyclePath C x K) =
      C (rightmostCocyclePath C' x k) (rightmostCocyclePath C x K)) :
    C' x (rightmostCocycleSuccessor C x) = ω' x ∧
      C x (rightmostCocycleSuccessor C' x) = ω x := by
  have hold := old_potential_le_new_of_unchanged_prefix ω ω' C C' hC hC' hr hr' x K hsame
  have hnew := new_potential_le_old_of_lowering ω ω' C C' hC hC' hr hr' hLower x k
  have heq := equal_potentials_of_boundary_comparison C C' hC hC' x
    (rightmostCocyclePath C' x k) (rightmostCocyclePath C x K) hold hnew hboundary
  constructor
  · apply first_edge_calibrated_of_total_comparison ω' ω C' C hC' hC hr' hr x K hK
    · intro j hj
      exact le_of_eq (hsame j hj).symm
    · exact heq.1
  · apply first_edge_calibrated_of_total_comparison ω ω' C C' hC hC' hr hr' x k hk
    · intro j hj
      exact hLower _
    · exact heq.2.symm

-- North boundary or return rules out the lower path's wrong first separation.
private theorem no_north_separation_before_boundary
    (ω ω' : Environment) (C C' : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hC' : is_additive C')
    (hr : recovers_environment ω C) (hr' : recovers_environment ω' C')
    (hLower : ∀ z, ω' z ≤ ω z) (V : Finset Lattice)
    (M1 M2 : ℤ) (hBox : ∀ z ∈ V, z.2 < M2)
    (hEdges : ∀ y : Lattice, y ∈ outsideLowerOrthants V →
      ∀ i : Fin 2, C' y (y + finiteEdgeStep i) = C y (y + finiteEdgeStep i))
    (x : Lattice) (N : ℕ)
    (hsame : ∀ j, j < N → ω' (rightmostCocyclePath C x j) =
      ω (rightmostCocyclePath C x j))
    (hbelow : x.2 < M2) (hend : rightmostCocyclePath C x N = (M1, M2))
    (hold : rightmostCocycleSuccessor C x = x + (1, 0))
    (hnew : rightmostCocycleSuccessor C' x = x + (0, 1)) : False := by
  let p := rightmostCocyclePath C x
  let q := rightmostCocyclePath C' x
  have hp0 : p 0 = x := by simp [p, rightmostCocyclePath]
  have hq0 : q 0 = x := by simp [q, rightmostCocyclePath]
  have hp : ∀ n, p (n + 1) = p n + (1, 0) ∨ p (n + 1) = p n + (0, 1) := by
    intro n
    simpa [p, rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_step C (p n)
  have hq : ∀ n, q (n + 1) = q n + (1, 0) ∨ q (n + 1) = q n + (0, 1) := by
    intro n
    simpa [q, rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_step C' (q n)
  have hp1 : p 1 = x + (1, 0) := by simpa [p, rightmostCocyclePath] using hold
  have hq1 : q 1 = x + (0, 1) := by simpa [q, rightmostCocyclePath] using hnew
  obtain ⟨k, hk, hkN, hhit⟩ := up_right_paths_meet_or_hit_north
    x p q N M1 M2 hp0 hq0 hp hq hp1 hq1 hbelow hend
  have hK : 0 < N := by omega
  have hcross : C' x (rightmostCocycleSuccessor C x) = ω' x ∧
      C x (rightmostCocycleSuccessor C' x) = ω x := by
    rcases hhit with hreturn | ⟨hy, hle⟩
    · have hboundary : C' (q k) (p k) = C (q k) (p k) := by
        rw [hreturn]
        have hc := hC (q k) (q k) (q k)
        have hc' := hC' (q k) (q k) (q k)
        linarith
      exact first_edges_cross_calibrated ω ω' C C' hC hC' hr hr' hLower x k k hk hk
        (fun j hj => hsame j (by omega)) hboundary
    · have hy' : q k = ((q k).1, M2) := by
        apply Prod.ext <;> simp [hy]
      have hboundary : C' (q k) (p N) = C (q k) (p N) := by
        change p N = _ at hend
        rw [hy', hend]
        exact rightmost_north_boundary_potential_eq C C' hC hC' V M2 _ M1 hBox hEdges hle
      exact first_edges_cross_calibrated ω ω' C C' hC hC' hr hr' hLower x N k hK hk
        hsame hboundary
  apply rightmost_north_step_conflicts_east_calibration ω' C' hr' x hnew
  simpa [hold] using hcross.1

-- East boundary or return supplies the distinct contradiction for the upper path.
private theorem no_east_separation_before_boundary
    (ω ω' : Environment) (C C' : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hC' : is_additive C')
    (hr : recovers_environment ω C) (hr' : recovers_environment ω' C')
    (hLower : ∀ z, ω' z ≤ ω z) (V : Finset Lattice)
    (M1 H : ℤ) (hBox : ∀ z ∈ V, z.1 < M1)
    (hEdges : ∀ y : Lattice, y ∈ outsideLowerOrthants V →
      ∀ i : Fin 2, C' y (y + finiteEdgeStep i) = C y (y + finiteEdgeStep i))
    (x : Lattice) (N : ℕ)
    (hsame : ∀ j, j < N → ω' (rightmostCocyclePath C x j) =
      ω (rightmostCocyclePath C x j))
    (hleft : x.1 < M1) (hend : rightmostCocyclePath C x N = (M1, H))
    (hold : rightmostCocycleSuccessor C x = x + (0, 1))
    (hnew : rightmostCocycleSuccessor C' x = x + (1, 0)) : False := by
  let p := rightmostCocyclePath C x
  let q := rightmostCocyclePath C' x
  have hp0 : p 0 = x := by simp [p, rightmostCocyclePath]
  have hq0 : q 0 = x := by simp [q, rightmostCocyclePath]
  have hp : ∀ n, p (n + 1) = p n + (1, 0) ∨ p (n + 1) = p n + (0, 1) := by
    intro n
    simpa [p, rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_step C (p n)
  have hq : ∀ n, q (n + 1) = q n + (1, 0) ∨ q (n + 1) = q n + (0, 1) := by
    intro n
    simpa [q, rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_step C' (q n)
  have hp1 : p 1 = x + (0, 1) := by simpa [p, rightmostCocyclePath] using hold
  have hq1 : q 1 = x + (1, 0) := by simpa [q, rightmostCocyclePath] using hnew
  obtain ⟨k, hk, hkN, hhit⟩ := up_right_paths_meet_or_hit_east
    x p q N M1 H hp0 hq0 hp hq hp1 hq1 hleft hend
  have hK : 0 < N := by omega
  have hcross : C' x (rightmostCocycleSuccessor C x) = ω' x ∧
      C x (rightmostCocycleSuccessor C' x) = ω x := by
    rcases hhit with hreturn | ⟨hy, hle⟩
    · have hboundary : C' (q k) (p k) = C (q k) (p k) := by
        rw [hreturn]
        have hc := hC (q k) (q k) (q k)
        have hc' := hC' (q k) (q k) (q k)
        linarith
      exact first_edges_cross_calibrated ω ω' C C' hC hC' hr hr' hLower x k k hk hk
        (fun j hj => hsame j (by omega)) hboundary
    · have hy' : q k = (M1, (q k).2) := by
        apply Prod.ext <;> simp [hy]
      have hboundary : C' (q k) (p N) = C (q k) (p N) := by
        change p N = _ at hend
        rw [hy', hend]
        exact rightmost_east_boundary_potential_eq C C' hC hC' V M1 _ H hBox hEdges hle
      exact first_edges_cross_calibrated ω ω' C C' hC hC' hr hr' hLower x N k hK hk
        hsame hboundary
  apply rightmost_north_step_conflicts_east_calibration ω C hr x hold
  simpa [hnew] using hcross.2

-- Iteration shifts a continuation to the corresponding time on the old path.
private theorem path_shift (C : Lattice → Lattice → ℝ) (x : Lattice) (m n : ℕ) :
    rightmostCocyclePath C (rightmostCocyclePath C x m) n =
      rightmostCocyclePath C x (m + n) := by
  change (rightmostCocycleSuccessor C)^[n] ((rightmostCocycleSuccessor C)^[m] x) =
    (rightmostCocycleSuccessor C)^[m + n] x
  rw [Nat.add_comm m n, Function.iterate_add_apply]

private theorem path_step (C : Lattice → Lattice → ℝ) (x : Lattice) (n : ℕ) :
    rightmostCocyclePath C x (n + 1) =
      rightmostCocycleSuccessor C (rightmostCocyclePath C x n) := by
  simp [rightmostCocyclePath, Function.iterate_succ_apply']

private theorem path_snd_mono (C : Lattice → Lattice → ℝ) (x : Lattice) :
    Monotone (fun n => (rightmostCocyclePath C x n).2) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [path_step]
  rcases rightmostCocycleSuccessor_step C (rightmostCocyclePath C x n) with h | h <;>
    simp only [h, Prod.snd_add] <;> omega

private theorem path_fst_mono (C : Lattice → Lattice → ℝ) (x : Lattice) :
    Monotone (fun n => (rightmostCocyclePath C x n).1) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [path_step]
  rcases rightmostCocycleSuccessor_step C (rightmostCocyclePath C x n) with h | h <;>
    simp only [h, Prod.fst_add] <;> omega

private theorem successors_eq_outside
    (C C' : Lattice → Lattice → ℝ) (V : Finset Lattice) (z : Lattice)
    (hz : z ∈ outsideLowerOrthants V)
    (hEdges : ∀ y : Lattice, y ∈ outsideLowerOrthants V →
      ∀ i : Fin 2, C' y (y + finiteEdgeStep i) = C y (y + finiteEdgeStep i)) :
    rightmostCocycleSuccessor C' z = rightmostCocycleSuccessor C z := by
  have he := hEdges z hz (0 : Fin 2)
  have hn := hEdges z hz (1 : Fin 2)
  simp [finiteEdgeStep] at he hn
  simp only [rightmostCocycleSuccessor, he, hn]

-- Equal-level paths can change their vertical order only at a common site.
private theorem path_order_of_no_wrong_step
    (A B : Lattice → Lattice → ℝ) (x : Lattice)
    (hwrong : ∀ n, rightmostCocyclePath A x n = rightmostCocyclePath B x n →
      ¬ (rightmostCocycleSuccessor A (rightmostCocyclePath A x n) =
            rightmostCocyclePath A x n + (1, 0) ∧
          rightmostCocycleSuccessor B (rightmostCocyclePath A x n) =
            rightmostCocyclePath A x n + (0, 1))) :
    ∀ n, (rightmostCocyclePath B x n).2 ≤ (rightmostCocyclePath A x n).2 := by
  have hlevel (D : Lattice → Lattice → ℝ) : ∀ n,
      (rightmostCocyclePath D x n).1 + (rightmostCocyclePath D x n).2 =
        x.1 + x.2 + (n : ℤ) := by
    intro n
    induction n with
    | zero => simp [rightmostCocyclePath]
    | succ n ih =>
      rw [path_step]
      rcases rightmostCocycleSuccessor_step D (rightmostCocyclePath D x n) with h | h <;>
        simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega
  intro n
  induction n with
  | zero => simp [rightmostCocyclePath]
  | succ n ih =>
    rw [path_step, path_step]
    let a := rightmostCocyclePath A x n
    let b := rightmostCocyclePath B x n
    change (rightmostCocycleSuccessor B b).2 ≤ (rightmostCocycleSuccessor A a).2
    change b.2 ≤ a.2 at ih
    have hsa := rightmostCocycleSuccessor_step A a
    have hsb := rightmostCocycleSuccessor_step B b
    by_cases heq : a = b
    · rw [← heq] at hsb ⊢
      rcases hsa with ha | ha <;> rcases hsb with hb | hb
      · simp only [ha, hb]
        exact le_rfl
      · exact False.elim (hwrong n heq ⟨ha, hb⟩)
      · simp only [ha, hb, Prod.snd_add]; omega
      · simp only [ha, hb]
        exact le_rfl
    · have hlt : b.2 < a.2 := by
        have ha := hlevel A n
        have hb := hlevel B n
        change a.1 + a.2 = x.1 + x.2 + (n : ℤ) at ha
        change b.1 + b.2 = x.1 + x.2 + (n : ℤ) at hb
        have hs : b.2 ≠ a.2 := by
          intro hs
          apply heq
          apply Prod.ext <;> omega
        omega
      rcases hsa with ha | ha <;> rcases hsb with hb | hb <;>
        simp only [ha, hb, Prod.snd_add] <;> omega

/-- Lowering weights away from two old rightmost paths, while preserving
outside increments, shields their continuations on opposite sides. This is the
finite north/east shielding argument in GRS, Appendix A, proof of A.5. -/
theorem rightmost_paths_outer_shielding
    (ω ω' : Environment) (C C' : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hC' : is_additive C')
    (hr : recovers_environment ω C) (hr' : recovers_environment ω' C')
    (hLower : ∀ z, ω' z ≤ ω z)
    (V : Finset Lattice) (ℓ M1 M2 H : ℤ) (nN nE : ℕ)
    (hBox : ∀ z ∈ V, z.1 < M1 ∧ z.2 < M2)
    (hOutside : ∀ z, z ∉ V → ω' z = ω z)
    (hAvoid : ∀ n, rightmostCocyclePath C 0 n ∉ V ∧
      rightmostCocyclePath C (0, ℓ) n ∉ V)
    (hNorth : rightmostCocyclePath C 0 nN = (M1, M2))
    (hEast : rightmostCocyclePath C (0, ℓ) nE = (M1, H))
    (hEdges : ∀ y : Lattice, y ∈ outsideLowerOrthants V →
      ∀ i : Fin 2, C' y (y + finiteEdgeStep i) = C y (y + finiteEdgeStep i)) :
    (∀ m n : ℕ, (rightmostCocyclePath C'
      (rightmostCocyclePath C 0 m) n).2 ≤
      (rightmostCocyclePath C (rightmostCocyclePath C 0 m) n).2) ∧
    (∀ m n : ℕ, (rightmostCocyclePath C
      (rightmostCocyclePath C (0, ℓ) m) n).2 ≤
      (rightmostCocyclePath C' (rightmostCocyclePath C (0, ℓ) m) n).2) := by
  -- At each old lower vertex a wrong first separation is impossible.
  have hNorthWrong (m : ℕ) :
      ¬ (rightmostCocycleSuccessor C (rightmostCocyclePath C 0 m) =
          rightmostCocyclePath C 0 m + (1, 0) ∧
        rightmostCocycleSuccessor C' (rightmostCocyclePath C 0 m) =
          rightmostCocyclePath C 0 m + (0, 1)) := by
    let z := rightmostCocyclePath C 0 m
    intro ⟨he, hn⟩
    by_cases hbelow : z.2 < M2
    · have hm : m < nN := by
        by_contra h
        have ht := path_snd_mono C 0 (show nN ≤ m by omega)
        dsimp only at ht
        rw [hNorth] at ht
        change (rightmostCocyclePath C 0 m).2 < M2 at hbelow
        omega
      have hsame : ∀ j, j < nN - m →
          ω' (rightmostCocyclePath C z j) = ω (rightmostCocyclePath C z j) := by
        intro j hj
        rw [show z = rightmostCocyclePath C 0 m from rfl, path_shift]
        exact hOutside _ (hAvoid (m + j)).1
      have hend : rightmostCocyclePath C z (nN - m) = (M1, M2) := by
        rw [show z = rightmostCocyclePath C 0 m from rfl, path_shift]
        have : m + (nN - m) = nN := by omega
        rw [this, hNorth]
      exact no_north_separation_before_boundary ω ω' C C' hC hC' hr hr' hLower
        V M1 M2 (fun a ha => (hBox a ha).2) hEdges z (nN - m) hsame hbelow hend he hn
    · have hz : z ∈ outsideLowerOrthants V := by
        change ∀ a ∈ V, ¬ z ≤ a
        intro a ha hz
        have hb := (hBox a ha).2
        have hz' := hz.2
        omega
      have hs := successors_eq_outside C C' V z hz hEdges
      rw [he, hn] at hs
      have hc := congrArg Prod.fst hs
      simp at hc
  -- The upper comparison uses the east boundary and the old north tie rule.
  have hEastWrong (m : ℕ) :
      ¬ (rightmostCocycleSuccessor C (rightmostCocyclePath C (0, ℓ) m) =
          rightmostCocyclePath C (0, ℓ) m + (0, 1) ∧
        rightmostCocycleSuccessor C' (rightmostCocyclePath C (0, ℓ) m) =
          rightmostCocyclePath C (0, ℓ) m + (1, 0)) := by
    let z := rightmostCocyclePath C (0, ℓ) m
    intro ⟨hn, he⟩
    by_cases hleft : z.1 < M1
    · have hm : m < nE := by
        by_contra h
        have ht := path_fst_mono C (0, ℓ) (show nE ≤ m by omega)
        dsimp only at ht
        rw [hEast] at ht
        change (rightmostCocyclePath C (0, ℓ) m).1 < M1 at hleft
        omega
      have hsame : ∀ j, j < nE - m →
          ω' (rightmostCocyclePath C z j) = ω (rightmostCocyclePath C z j) := by
        intro j hj
        rw [show z = rightmostCocyclePath C (0, ℓ) m from rfl, path_shift]
        exact hOutside _ (hAvoid (m + j)).2
      have hend : rightmostCocyclePath C z (nE - m) = (M1, H) := by
        rw [show z = rightmostCocyclePath C (0, ℓ) m from rfl, path_shift]
        have : m + (nE - m) = nE := by omega
        rw [this, hEast]
      exact no_east_separation_before_boundary ω ω' C C' hC hC' hr hr' hLower
        V M1 H (fun a ha => (hBox a ha).1) hEdges z (nE - m) hsame hleft hend hn he
    · have hz : z ∈ outsideLowerOrthants V := by
        change ∀ a ∈ V, ¬ z ≤ a
        intro a ha hz
        have hb := (hBox a ha).1
        have hz' := hz.1
        omega
      have hs := successors_eq_outside C C' V z hz hEdges
      rw [hn, he] at hs
      have hc := congrArg Prod.fst hs
      simp at hc
  constructor
  · intro m
    apply path_order_of_no_wrong_step C C' (rightmostCocyclePath C 0 m)
    intro n heq hwrong
    rw [path_shift] at hwrong
    exact hNorthWrong (m + n) hwrong
  · intro m
    apply path_order_of_no_wrong_step C' C (rightmostCocyclePath C (0, ℓ) m)
    intro n heq ⟨he, hn⟩
    rw [heq, path_shift] at he hn
    exact hEastWrong (m + n) ⟨hn, he⟩

end LPP.Busemann
