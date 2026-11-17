/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPathCorridorCrossing
public import Busemann.Process.RightmostPaths
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! A finite corridor crossing carries one calibrated maximizing path. -/

@[expose] public section
open LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

/-- The finite corridor crossing carries one calibrated path with the exact
entry and exit, and with every noninitial collected vertex in the corridor.
This composes the finite geometry of GRS, arXiv:1510.00860v1, Appendix A.4,
lines 1616–1632, with the rightmost-prefix calibration. -/
theorem exists_calibrated_rightmost_corridor_crossing
    (ω' : Environment) (C D : Lattice → Lattice → ℝ)
    (hD : is_additive D) (hRecD : recovers_environment ω' D)
    (m ell : ℕ) (hm : 0 < m) (hmell : m < ell)
    (M1 M2 a1 a2 : ℤ) (hTop : (ell : ℤ) < M2)
    (nL nM nU : ℕ)
    (hNorthL : rightmostCocyclePath C 0 nL = (M1, M2))
    (hNorthM : rightmostCocyclePath C (0, (m : ℤ)) nM = (a2, M2))
    (hNorthU : rightmostCocyclePath C (0, (ell : ℤ)) nU = (a1, M2))
    (hDisjointLM : ∀ r s : ℕ,
      rightmostCocyclePath C 0 r ≠
        rightmostCocyclePath C (0, (m : ℤ)) s)
    (hDisjointMU : ∀ r s : ℕ,
      rightmostCocyclePath C (0, (m : ℤ)) r ≠
        rightmostCocyclePath C (0, (ell : ℤ)) s)
    (hMiddleTail : ∀ r : ℕ,
      rightmostCocyclePath D (a2, M2) r =
        rightmostCocyclePath C (a2, M2) r)
    (hLowerBarrier : ∀ r s : ℕ,
      (rightmostCocyclePath D (rightmostCocyclePath C 0 r) s).2 ≤
        (rightmostCocyclePath C (rightmostCocyclePath C 0 r) s).2)
    (hUpperBarrier : ∀ r s : ℕ,
      (rightmostCocyclePath C
        (rightmostCocyclePath C (0, (ell : ℤ)) r) s).2 ≤
      (rightmostCocyclePath D
        (rightmostCocyclePath C (0, (ell : ℤ)) r) s).2)
    (R : Finset Lattice)
    (hR : ∀ z : Lattice, z ∈ R ↔
      0 < z.1 ∧ z.2 < M2 ∧
      ∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
        (rightmostCocyclePath C 0 n).2 < z.2 ∧
        (n < ell ∨ z.2 <
          (rightmostCocyclePath C (0, (ell : ℤ)) (n - ell)).2))
    (v : Lattice)
    (hOutside : v ∉ Set.Icc (0 : Lattice) (M1, M2))
    (hWestOrSouth : v.1 ≤ 0 ∨ v.2 ≤ 0)
    (N k : ℕ)
    (hMeet : rightmostCocyclePath D v N =
      rightmostCocyclePath D (a2, M2) k) :
    ∃ entry exit : ℕ, ∃ j i : ℤ,
      0 < entry ∧ entry < exit ∧ exit ≤ N ∧
      0 < j ∧ j < (ell : ℤ) ∧
      a1 < i ∧ i < M1 ∧ 0 < i ∧
      rightmostCocyclePath D v entry = (0, j) ∧
      rightmostCocyclePath D v (entry + 1) = (1, j) ∧
      rightmostCocyclePath D v exit = (i, M2) ∧
      (∀ t : ℕ, entry < t →
        0 < (rightmostCocyclePath D v t).1) ∧
      (∀ t : ℕ, t < exit →
        (rightmostCocyclePath D v t).2 < M2) ∧
      (∀ t : ℕ, entry < t → t < exit →
        rightmostCocyclePath D v t ∈ R) ∧
      ∃ p : LPPDifferentiability.Path (0, j)
          (i.toNat, (M2 - j).toNat),
        (∀ r : Fin (i.toNat + (M2 - j).toNat + 1),
          p.vertex r = rightmostCocyclePath D v (entry + r.val)) ∧
        (∀ r : Fin (i.toNat + (M2 - j).toNat),
          D (p.vertex r.castSucc) (p.vertex r.succ) =
            ω' (p.vertex r.castSucc)) ∧
        (∀ r : Fin (i.toNat + (M2 - j).toNat), 0 < r.val →
          p.vertex r.castSucc ∈ R) ∧
        pathWeight ω' p = D (0, j) (i, M2) ∧
        pathWeight ω' p =
          lastPassage ω' (0, j) (i.toNat, (M2 - j).toNat) := by
  obtain ⟨entry, exit, j, i, hEntryPos, hEntryExit, hExitN, hJPos, hJell,
      ha1i, hiM1, hiPos, hEntry, hNext, hExit, hAfterX, hBeforeY, hInside⟩ :=
    exists_rightmost_corridor_entry_exit C D m ell hm hmell M1 M2 a1 a2
      hTop nL nM nU hNorthL hNorthM hNorthU hDisjointLM hDisjointMU
      hMiddleTail hLowerBarrier hUpperBarrier R hR v hOutside hWestOrSouth
      N k hMeet
  let T := exit - entry
  have hEntryAddT : entry + T = exit := by dsimp [T]; omega
  have hRestart (r : ℕ) :
      rightmostCocyclePath D (0, j) r =
        rightmostCocyclePath D v (entry + r) := by
    rw [← hEntry]
    change (rightmostCocycleSuccessor D)^[r]
        ((rightmostCocycleSuccessor D)^[entry] v) =
      (rightmostCocycleSuccessor D)^[entry + r] v
    rw [Nat.add_comm entry r, Function.iterate_add_apply]
  obtain ⟨q, hTrace, hPotential, hMaximum⟩ :=
    exists_rightmostCocyclePath_prefix ω' D hD hRecD (0, j) T
  let oldN := q.1.val + (T - q.1.val)
  let newN := i.toNat + (M2 - j).toNat
  have hKle : q.1.val ≤ T := by have hk := q.1.isLt; omega
  have hOldN : oldN = T := by
    dsimp [oldN]
    exact Nat.add_sub_of_le hKle
  have hLastBound : T < oldN + 1 := by
    dsimp only [oldN]
    have hlen := Nat.add_sub_of_le hKle
    omega
  let lastIndex : Fin (oldN + 1) := ⟨T, hLastBound⟩
  have hTraceEnd : q.2.vertex lastIndex =
      rightmostCocyclePath D (0, j) T := by
    have ht := hTrace T (by have hlen := Nat.add_sub_of_le hKle; omega)
    simpa only [lastIndex] using ht
  have hFinLast : lastIndex = Fin.last oldN := by
    apply Fin.ext
    simp only [Fin.val_last, lastIndex]
    exact hOldN.symm
  have hFinish : q.2.vertex lastIndex =
      (0, j) + ((q.1.val : ℤ), ((T - q.1.val : ℕ) : ℤ)) := by
    have hf := congrArg q.2.vertex hFinLast
    rw [q.2.finish] at hf
    simpa only [lastIndex] using hf
  have hPrefixEnd : q.2.vertex lastIndex = (i, M2) := by
    calc
      q.2.vertex lastIndex = rightmostCocyclePath D (0, j) T := hTraceEnd
      _ = rightmostCocyclePath D v (entry + T) := hRestart T
      _ = rightmostCocyclePath D v exit := by rw [← hEntryAddT]
      _ = (i, M2) := hExit
  have hPoint :
      (0, j) + ((q.1.val : ℤ), ((T - q.1.val : ℕ) : ℤ)) = (i, M2) :=
    hFinish.symm.trans hPrefixEnd
  have hX : (q.1.val : ℤ) = i := by
    simpa only [Prod.fst_add, zero_add] using congrArg Prod.fst hPoint
  have hY : j + ((T - q.1.val : ℕ) : ℤ) = M2 := by
    simpa only [Prod.snd_add] using congrArg Prod.snd hPoint
  have hKValue : q.1.val = i.toNat := by
    apply Int.ofNat.inj
    have hiCast : (i.toNat : ℤ) = i := Int.toNat_of_nonneg (by omega)
    exact hX.trans hiCast.symm
  have hKRestInt : ((T - q.1.val : ℕ) : ℤ) = M2 - j := by omega
  have hKRest : T - q.1.val = (M2 - j).toNat := by
    apply Int.ofNat.inj
    have hRestCast : ((M2 - j).toNat : ℤ) = M2 - j :=
      Int.toNat_of_nonneg (by omega)
    exact hKRestInt.trans hRestCast.symm
  have hNewN : newN = T := by
    dsimp [newN]
    rw [← hKValue, ← hKRest]
    exact Nat.add_sub_of_le hKle
  have hIndex : oldN = newN := hOldN.trans hNewN.symm
  have hIndexSucc : oldN + 1 = newN + 1 := congrArg Nat.succ hIndex
  have hCastSucc (r : Fin newN) :
      Fin.cast hIndexSucc.symm r.succ = (Fin.cast hIndex.symm r).succ := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_succ]
  have hCastCastSucc (r : Fin newN) :
      Fin.cast hIndexSucc.symm r.castSucc =
        (Fin.cast hIndex.symm r).castSucc := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_castSucc]
  have hCastLast (r : Fin (newN + 1)) :
      Fin.cast hIndexSucc.symm r = ⟨r.val, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_cast]
  let p : LPPDifferentiability.Path (0, j) (i.toNat, (M2 - j).toNat) := {
    vertex := fun r => q.2.vertex (Fin.cast hIndexSucc.symm r)
    start := by
      change q.2.vertex (Fin.cast hIndexSucc.symm 0) = (0, j)
      have hz : Fin.cast hIndexSucc.symm 0 = (0 : Fin (oldN + 1)) := by
        apply Fin.ext
        rfl
      rw [hz]
      exact q.2.start
    finish := by
      change q.2.vertex (Fin.cast hIndexSucc.symm (Fin.last newN)) =
        (0, j) + ((i.toNat : ℤ), ((M2 - j).toNat : ℤ))
      have hLast :
          Fin.cast hIndexSucc.symm (Fin.last newN) = Fin.last oldN := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_last]
        exact hIndex.symm
      rw [hLast, q.2.finish]
      apply Prod.ext
      · simp only [Prod.fst_add]
        exact congrArg (fun n : ℕ => (0 : ℤ) + (n : ℤ)) hKValue
      · simp only [Prod.snd_add]
        exact congrArg (fun n : ℕ => j + (n : ℤ)) hKRest
    step := by
      intro r
      rw [hCastSucc r, hCastCastSucc r]
      exact q.2.step (Fin.cast hIndex.symm r)
  }
  have hPathTrace (r : Fin (newN + 1)) :
      p.vertex r = rightmostCocyclePath D v (entry + r.val) := by
    change q.2.vertex (Fin.cast hIndexSucc.symm r) =
      rightmostCocyclePath D v (entry + r.val)
    have hrBound : r.val < oldN + 1 := by omega
    have hrTrace : r.val < q.1.val + (T - q.1.val) + 1 := by
      simpa only [oldN] using hrBound
    rw [hCastLast r]
    calc
      q.2.vertex ⟨r.val, hrBound⟩ =
          rightmostCocyclePath D (0, j) r.val := hTrace r.val hrTrace
      _ = rightmostCocyclePath D v (entry + r.val) := hRestart r.val
  have hIterateStep (n : ℕ) :
      rightmostCocyclePath D v (n + 1) =
        rightmostCocycleSuccessor D (rightmostCocyclePath D v n) := by
    simp only [rightmostCocyclePath, Function.iterate_succ_apply']
  have hCalibratedEdge (r : Fin newN) :
      D (p.vertex r.castSucc) (p.vertex r.succ) = ω' (p.vertex r.castSucc) := by
    calc
      D (p.vertex r.castSucc) (p.vertex r.succ) =
          D (rightmostCocyclePath D v (entry + r.val))
            (rightmostCocycleSuccessor D
              (rightmostCocyclePath D v (entry + r.val))) := by
        rw [hPathTrace r.castSucc, hPathTrace r.succ]
        have hStartIndex : entry + r.castSucc.val = entry + r.val := by rfl
        have hEndIndex : entry + r.succ.val = entry + r.val + 1 := by
          simp [Nat.add_assoc]
        rw [hStartIndex, hEndIndex, hIterateStep]
      _ = ω' (rightmostCocyclePath D v (entry + r.val)) :=
        rightmostCocycleSuccessor_calibrated ω' D hRecD _
      _ = ω' (p.vertex r.castSucc) := by
        have ht := congrArg ω' (hPathTrace r.castSucc)
        simpa only [Fin.val_castSucc] using ht.symm
  have hCollectedInside (r : Fin newN) (hr : 0 < r.val) :
      p.vertex r.castSucc ∈ R := by
    rw [hPathTrace r.castSucc]
    have hrltT : r.val < T := by
      calc
        r.val < newN := r.isLt
        _ = T := hNewN
    have hEntryBefore : entry < entry + r.castSucc.val := by
      rw [show r.castSucc.val = r.val by rfl]
      omega
    have hBeforeExit : entry + r.castSucc.val < exit := by
      rw [show r.castSucc.val = r.val by rfl, ← hEntryAddT]
      exact Nat.add_lt_add_left hrltT entry
    exact hInside (entry + r.castSucc.val) hEntryBefore hBeforeExit
  have hPathWeight : pathWeight ω' p = pathWeight ω' q.2 := by
    unfold pathWeight
    rw [← Fin.sum_congr' _ hIndex.symm]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
  refine ⟨entry, exit, j, i, hEntryPos, hEntryExit, hExitN, hJPos, hJell,
    ha1i, hiM1, hiPos, hEntry, hNext, hExit, hAfterX, hBeforeY, hInside,
    p, hPathTrace, hCalibratedEdge, hCollectedInside, ?_, ?_⟩
  · calc
      pathWeight ω' p = pathWeight ω' q.2 := hPathWeight
      _ = D (0, j) (rightmostCocyclePath D (0, j) T) := hPotential
      _ = D (0, j) (i, M2) := by
        rw [hRestart T, hEntryAddT, hExit]
  · calc
      pathWeight ω' p = pathWeight ω' q.2 := hPathWeight
      _ = lastPassage ω' (0, j) (q.1.val, T - q.1.val) := hMaximum
      _ = lastPassage ω' (0, j) (i.toNat, (M2 - j).toNat) := by
        rw [show (q.1.val, T - q.1.val) =
          (i.toNat, (M2 - j).toNat) from Prod.ext hKValue hKRest]

end LPP.Busemann
