/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Literal finite count for the source stage-index itineraries. -/

public section

namespace LPPDifferentiability

private def stageStepCode (dx dy : ℤ) : Fin 3 × Fin 5 :=
  (⟨dx.toNat % 3, Nat.mod_lt _ (by omega)⟩,
    ⟨(dy + 2).toNat % 5, Nat.mod_lt _ (by omega)⟩)

private def stageStepDecode (w : Fin 3 × Fin 5) : ℤ × ℤ :=
  ((w.1.val : ℤ), (w.2.val : ℤ) - 2)

private def stageSequenceOfCode {N : ℕ} (w : Fin N → Fin 3 × Fin 5) :
    Fin (N + 1) → ℤ × ℤ := fun i =>
  ((∑ j : Fin i.val, ((w ⟨j.val, by omega⟩).1.val : ℤ)),
    ∑ j : Fin i.val, (((w ⟨j.val, by omega⟩).2.val : ℤ) - 2))

private def stageCodeOfSequence {N : ℕ} (c : Fin (N + 1) → ℤ × ℤ) :
    Fin N → Fin 3 × Fin 5 := fun i =>
  stageStepCode ((c i.succ).1 - (c i.castSucc).1)
    ((c i.succ).2 - (c i.castSucc).2)

private theorem stageSequenceOfCode_start {N : ℕ}
    (w : Fin N → Fin 3 × Fin 5) :
    stageSequenceOfCode w 0 = (0, 0) := by
  change
    ((∑ j : Fin 0, ((w ⟨j.val, by omega⟩).1.val : ℤ)),
      ∑ j : Fin 0, (((w ⟨j.val, by omega⟩).2.val : ℤ) - 2)) = (0, 0)
  rw [Fin.sum_univ_zero, Fin.sum_univ_zero]

private theorem stageSequenceOfCode_succ {N : ℕ}
    (w : Fin N → Fin 3 × Fin 5) (i : Fin N) :
    stageSequenceOfCode w i.succ =
      stageSequenceOfCode w i.castSucc + stageStepDecode (w i) := by
  simp [stageSequenceOfCode, stageStepDecode, Fin.sum_univ_castSucc]
  ring

private theorem stageSequenceOfCode_admissible {N : ℕ}
    (w : Fin N → Fin 3 × Fin 5) :
    stageSequenceOfCode w 0 = (0, 0) ∧
      ∀ i : Fin N,
        ((stageSequenceOfCode w i.succ).1 -
            (stageSequenceOfCode w i.castSucc).1 = 0 ∨
          (stageSequenceOfCode w i.succ).1 -
            (stageSequenceOfCode w i.castSucc).1 = 1 ∨
          (stageSequenceOfCode w i.succ).1 -
            (stageSequenceOfCode w i.castSucc).1 = 2) ∧
          |(stageSequenceOfCode w i.succ).2 -
            (stageSequenceOfCode w i.castSucc).2| ≤ 2 := by
  constructor
  · exact stageSequenceOfCode_start w
  · intro i
    rw [stageSequenceOfCode_succ]
    simp only [Prod.fst_add, Prod.snd_add, stageStepDecode]
    have h3 := (w i).1.isLt
    have h5 := (w i).2.isLt
    constructor
    · omega
    · rw [abs_le]
      constructor <;> omega

private theorem stageStepCode_decode {dx dy : ℤ}
    (hdx : dx = 0 ∨ dx = 1 ∨ dx = 2) (hdy : |dy| ≤ 2) :
    stageStepDecode (stageStepCode dx dy) = (dx, dy) := by
  have hdx0 : 0 ≤ dx := by omega
  have hdyBounds := abs_le.mp hdy
  have hdy0 : 0 ≤ dy + 2 := by omega
  have hdxcast : (dx.toNat : ℤ) = dx := Int.toNat_of_nonneg hdx0
  have hdycast : ((dy + 2).toNat : ℤ) = dy + 2 :=
    Int.toNat_of_nonneg hdy0
  have hdxltZ : (dx.toNat : ℤ) < 3 := by
    rw [hdxcast]
    rcases hdx with h | h | h <;> omega
  have hdyltZ : ((dy + 2).toNat : ℤ) < 5 := by
    rw [hdycast]
    omega
  have hdxlt : dx.toNat < 3 := by exact_mod_cast hdxltZ
  have hdylt : (dy + 2).toNat < 5 := by exact_mod_cast hdyltZ
  simp [stageStepDecode, stageStepCode, Nat.mod_eq_of_lt hdxlt,
    Nat.mod_eq_of_lt hdylt, hdxcast, hdycast]

private theorem stageCodeOfSequence_reconstruct {N : ℕ}
    (c : Fin (N + 1) → ℤ × ℤ) (hc0 : c 0 = (0, 0))
    (hsteps : ∀ i : Fin N,
      ((c i.succ).1 - (c i.castSucc).1 = 0 ∨
        (c i.succ).1 - (c i.castSucc).1 = 1 ∨
        (c i.succ).1 - (c i.castSucc).1 = 2) ∧
        |(c i.succ).2 - (c i.castSucc).2| ≤ 2) :
    stageSequenceOfCode (stageCodeOfSequence c) = c := by
  funext i
  have hpoint : ∀ j : ℕ, ∀ hj : j ≤ N,
      stageSequenceOfCode (stageCodeOfSequence c) ⟨j, by omega⟩ =
        c ⟨j, by omega⟩ := by
    intro j
    induction j with
    | zero =>
        intro hj
        simpa [stageSequenceOfCode] using hc0.symm
    | succ j ih =>
        intro hj
        let k : Fin N := ⟨j, by omega⟩
        have hprev := ih (by omega)
        have hcode := stageStepCode_decode (hsteps k).1 (hsteps k).2
        have hnext : stageSequenceOfCode (stageCodeOfSequence c)
            ⟨j + 1, by omega⟩ =
            stageSequenceOfCode (stageCodeOfSequence c) ⟨j, by omega⟩ +
              stageStepDecode (stageCodeOfSequence c k) := by
          simpa [stageSequenceOfCode] using
            stageSequenceOfCode_succ (stageCodeOfSequence c) k
        have hcode' : stageStepDecode (stageCodeOfSequence c k) =
            ((c ⟨j + 1, by omega⟩).1 - (c ⟨j, by omega⟩).1,
              (c ⟨j + 1, by omega⟩).2 - (c ⟨j, by omega⟩).2) := by
          simpa [stageCodeOfSequence, k] using hcode
        rw [hnext, hprev, hcode']
        apply Prod.ext
        · rw [Prod.fst_add]
          omega
        · rw [Prod.snd_add]
          omega
  simpa using hpoint i.val (by omega)

private theorem stageSequenceOfCode_injective {N : ℕ} :
    Function.Injective (stageSequenceOfCode (N := N)) := by
  intro w v h
  funext i
  have hpre := congrArg (fun c => c i.castSucc) h
  have hnext := congrArg (fun c => c i.succ) h
  have hw := stageSequenceOfCode_succ w i
  have hv := stageSequenceOfCode_succ v i
  have hfst := congrArg Prod.fst hnext
  have hfstPre := congrArg Prod.fst hpre
  have hsnd := congrArg Prod.snd hnext
  have hsndPre := congrArg Prod.snd hpre
  rw [hw, hv, Prod.fst_add, Prod.fst_add] at hfst
  rw [hw, hv, Prod.snd_add, Prod.snd_add] at hsnd
  have hlong : ((w i).1.val : ℤ) = (v i).1.val := by
    simp only [stageStepDecode] at hfst
    omega
  have htrans : ((w i).2.val : ℤ) = (v i).2.val := by
    simp only [stageStepDecode] at hsnd
    omega
  apply Prod.ext
  · apply Fin.ext
    exact_mod_cast hlong
  · apply Fin.ext
    exact_mod_cast htrans

/-- The literal set of stage-index sequences has its exact finite count.
Each of its `N` increments is encoded by one of the `3 × 5` source-allowed
increments; partial sums from zero reconstruct every sequence uniquely. -/
theorem exists_stage_itinerary_finset (N : ℕ) :
    ∃ C : Finset (Fin (N + 1) → ℤ × ℤ),
      (∀ c, c ∈ C ↔ c 0 = (0, 0) ∧
        ∀ i : Fin N,
          ((c i.succ).1 - (c i.castSucc).1 = 0 ∨
            (c i.succ).1 - (c i.castSucc).1 = 1 ∨
            (c i.succ).1 - (c i.castSucc).1 = 2) ∧
            |(c i.succ).2 - (c i.castSucc).2| ≤ 2) ∧
      C.card = 15 ^ N := by
  classical
  let C : Finset (Fin (N + 1) → ℤ × ℤ) :=
    Finset.univ.image (stageSequenceOfCode (N := N))
  refine ⟨C, ?_, ?_⟩
  · intro c
    change c ∈ Finset.univ.image (stageSequenceOfCode (N := N)) ↔ _
    constructor
    · intro hc
      rcases Finset.mem_image.mp hc with ⟨w, -, rfl⟩
      exact stageSequenceOfCode_admissible w
    · rintro ⟨hc0, hsteps⟩
      rw [Finset.mem_image]
      refine ⟨stageCodeOfSequence c, Finset.mem_univ _, ?_⟩
      exact stageCodeOfSequence_reconstruct c hc0 hsteps
  · change (Finset.univ.image (stageSequenceOfCode (N := N))).card = 15 ^ N
    rw [Finset.card_image_of_injective _ stageSequenceOfCode_injective]
    simp [Fintype.card_prod, Fintype.card_fin]

end LPPDifferentiability
