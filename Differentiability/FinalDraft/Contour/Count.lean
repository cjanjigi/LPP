/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Contour.Definitions
import LPP_Foundations.Model.LatticeWalkWordEncoding
import Mathlib.Tactic

/-! A count of unrooted directed circuits through the positive ray.
Start each circuit at a ray edge and count nonbacktracking continuations. -/

public section

namespace LPPDifferentiability

private theorem unit_edge_words_from_letter {A : Type*} [Fintype A] [DecidableEq A]
    (forbidden : A → A) (n : ℕ) :
    ∃ T : A → Finset (List A), ∀ a,
      (∀ w, w ∈ T a ↔ w.length = n ∧
        (a :: w).IsChain (fun x y => y ≠ forbidden x)) ∧
      (T a).card = (Fintype.card A - 1) ^ n := by
  classical
  induction n with
  | zero =>
    refine ⟨fun _ => {[]}, fun a => ⟨?_, ?_⟩⟩
    · intro w
      rw [Finset.mem_singleton, List.length_eq_zero_iff]
      constructor
      · intro hw
        subst w
        exact ⟨rfl, List.isChain_singleton a⟩
      · exact And.left
    · simp only [Finset.card_singleton, pow_zero]
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    let S : A → Finset (List A) := fun a =>
      (Finset.univ.erase (forbidden a)).biUnion fun b => (T b).image (List.cons b)
    refine ⟨S, fun a => ⟨?_, ?_⟩⟩
    · intro w
      cases w with
      | nil =>
        simp only [S, Finset.mem_biUnion, Finset.mem_image, List.cons_ne_nil,
          and_false, exists_false, List.length_nil, false_and, Nat.zero_ne_add_one]
      | cons b w =>
        simp only [S, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ,
          and_true, Finset.mem_image, List.cons.injEq,
          hT, List.length_cons, Nat.add_right_cancel_iff, List.isChain_cons_cons]
        aesop
    · change ((Finset.univ.erase (forbidden a)).biUnion
        fun b => (T b).image (List.cons b)).card = _
      have hdis : (↑(Finset.univ.erase (forbidden a)) : Set A).PairwiseDisjoint
          (fun b => (T b).image (List.cons b)) := by
        intro b _ c _ hbc
        apply Finset.disjoint_left.mpr
        intro w hwb hwc
        obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hwb
        obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hwc
        exact hbc (List.cons.inj (hu.trans hv.symm)).1
      rw [Finset.card_biUnion hdis]
      simp only [Finset.card_image_of_injective _ List.cons_injective, (hT _).2]
      rw [Finset.sum_const_nat (fun _ _ => rfl),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, pow_succ]
      exact Nat.mul_comm _ _

private theorem exists_finset_walks_first_edge (m : ℕ) (hm : 0 < m)
    (e : Lattice × Lattice) :
    ∃ W : Finset (Fin (m + 1) → Lattice),
      (∀ v, v ∈ W ↔ squareCircuitEdge v ⟨0, hm⟩ = e ∧
        (∀ i, IsDualUnitEdge (squareCircuitEdge v i)) ∧
        (∀ (i : ℕ) (hi : i + 2 ≤ m),
          v ⟨i + 2, by omega⟩ ≠ v ⟨i, by omega⟩)) ∧
      W.card ≤ 3 ^ (m - 1) := by
  classical
  obtain ⟨T, hT⟩ := unit_edge_words_from_letter (fun a : Fin 4 => a + 2) (m - 1)
  obtain ⟨encode, hinj, hencode⟩ := exists_injective_lattice_walk_direction_lists e.1 m
  let S : Set (Fin (m + 1) → Lattice) := {v |
    squareCircuitEdge v ⟨0, hm⟩ = e ∧
      (∀ i, IsDualUnitEdge (squareCircuitEdge v i)) ∧
      (∀ (i : ℕ) (hi : i + 2 ≤ m), v ⟨i + 2, by omega⟩ ≠ v ⟨i, by omega⟩)}
  let p (v : S) : {w : Fin (m + 1) → Lattice // w 0 = e.1 ∧
      ∀ i : Fin m, IsDualUnitEdge (squareCircuitEdge w i)} :=
    ⟨v.val, congrArg Prod.fst v.property.1, v.property.2.1⟩
  let a : Fin 4 := if e.2 - e.1 = (1, 0) then 0 else if e.2 - e.1 = (0, 1) then 1
    else if e.2 - e.1 = (-1, 0) then 2 else 3
  have hfirst (v : S) : a :: (encode (p v)).tail = encode (p v) := by
    obtain ⟨d, hd, hvals⟩ := (hencode (p v)).2.1
    have hd₀ : d ⟨0, hm⟩ = a := by
      have hs := hvals ⟨0, hm⟩
      have hEq := v.property.1
      have hdiff : v.val ⟨1, by omega⟩ - v.val 0 = e.2 - e.1 :=
        congrArg (fun e : Lattice × Lattice => e.2 - e.1) hEq
      dsimp [p] at hs
      rw [hdiff] at hs
      rcases hs with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨h, hs⟩ <;> norm_num [a, h, hs]
    rw [hd, ← hd₀]
    have hn : List.ofFn d ≠ [] := fun h => hm.ne' (List.ofFn_eq_nil_iff.mp h)
    rw [← List.head_ofFn hn]
    exact List.cons_head_tail hn
  let f (v : S) : {w // w ∈ T a} := ⟨(encode (p v)).tail, (hT a).1 _ |>.mpr (by
    refine ⟨?_, ?_⟩
    · rw [List.length_tail, (hencode (p v)).1]
    · rw [hfirst v]
      exact (hencode (p v)).2.2 v.property.2.2)⟩
  have hf : Function.Injective f := by
    intro v w h
    have htail := congrArg Subtype.val h
    change (encode (p v)).tail = (encode (p w)).tail at htail
    apply Subtype.ext
    have hc := congrArg (List.cons a) htail
    rw [hfirst v, hfirst w] at hc
    have hwalk := congrArg (fun x => x.val) (hinj hc)
    exact hwalk
  let : Finite S := Finite.of_injective f hf
  let : Fintype S := Fintype.ofFinite S
  refine ⟨S.toFinset, fun v => Set.mem_toFinset, ?_⟩
  rw [Set.toFinset_card]
  calc
    Fintype.card S ≤ Fintype.card {w // w ∈ T a} := Fintype.card_le_of_injective f hf
    _ = (T a).card := Fintype.card_coe _
    _ = 3 ^ (m - 1) := by simpa only [Fintype.card_fin, Nat.reduceSub] using (hT a).2

private theorem circuit_no_return {m : ℕ} {v : Fin (m + 1) → Lattice}
    (hc : IsSquareCircuit v) (i : ℕ) (hi : i + 2 ≤ m) :
    v ⟨i + 2, by omega⟩ ≠ v ⟨i, by omega⟩ := by
  intro h
  exact hc.2.2.2 ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (Prod.ext rfl h.symm)

private theorem exists_circuit_starting_at_edge {m : ℕ} {v : Fin (m + 1) → Lattice}
    (hc : IsSquareCircuit v) (k : Fin m) :
    ∃ w : Fin (m + 1) → Lattice, IsSquareCircuit w ∧
      squareCircuitEdge w ⟨0, Nat.zero_lt_of_lt k.isLt⟩ = squareCircuitEdge v k ∧
      squareCircuitCycle w = squareCircuitCycle v := by
  have hm : 0 < m := Nat.zero_lt_of_lt k.isLt
  let p (i : Fin (m + 1)) : Fin m := ⟨(i.val + k.val) % m, Nat.mod_lt _ hm⟩
  let w (i : Fin (m + 1)) := v (p i).castSucc
  have hclosed : w 0 = w (Fin.last m) := by
    apply congrArg (fun j : Fin m => v j.castSucc)
    apply Fin.ext
    change (0 + k.val) % m = (m + k.val) % m
    rw [zero_add, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
  have hstep (i : Fin m) :
      squareCircuitEdge w i = squareCircuitEdge v (p i.castSucc) := by
    change (w i.castSucc, w i.succ) = (v (p i.castSucc).castSucc, v (p i.castSucc).succ)
    refine Prod.ext rfl ?_
    let j := p i.castSucc
    change v (p i.succ).castSucc = v j.succ
    have hsucc : (p i.succ).val = (j.val + 1) % m := by
      change ((i.val + 1) + k.val) % m = (((i.val + k.val) % m) + 1) % m
      rw [Nat.add_right_comm, Nat.mod_add_mod]
    by_cases hj : j.val + 1 < m
    · have heq : (p i.succ).castSucc = j.succ := Fin.ext (by
        simp only [Fin.val_castSucc, Fin.val_succ, hsucc, Nat.mod_eq_of_lt hj])
      rw [heq]
    · have hj' : j.val + 1 = m := by omega
      have hzero : (p i.succ).castSucc = 0 := Fin.ext (by
        simp only [Fin.val_castSucc, hsucc, hj', Nat.mod_self, Fin.val_zero])
      have hlast : j.succ = Fin.last m := Fin.ext hj'
      rw [hzero, hlast, hc.1]
  have hp : Function.Injective (fun i : Fin m => p i.castSucc) := by
    intro i j h
    have heq : (i.val + k.val) % m = (j.val + k.val) % m := congrArg Fin.val h
    have hcancel := congrArg (fun n : ℕ => (n + (m - k.val)) % m) heq
    have hk : k.val + (m - k.val) = m := by omega
    simp only [Nat.mod_add_mod, Nat.add_assoc, hk, Nat.add_mod_right,
      Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hcancel
    exact Fin.ext hcancel
  have hcycle : squareCircuitCycle w = squareCircuitCycle v := by
    apply Cycle.coe_eq_coe.mpr
    apply List.IsRotated.symm
    refine ⟨k.val, ?_⟩
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      rw [List.getElem_rotate]
      simp only [List.length_ofFn, List.getElem_ofFn]
      exact (hstep ⟨i, by simpa only [List.length_ofFn, List.length_rotate] using hi⟩).symm
  refine ⟨w, ⟨hclosed, fun i => hstep i ▸ hc.2.1 _, ?_, ?_⟩, ?_, hcycle⟩
  · intro i j h
    rw [hstep, hstep] at h
    exact hp (hc.2.2.1 h)
  · intro i j h
    rw [hstep, hstep] at h
    exact hc.2.2.2 _ _ h
  · rw [hstep]
    congr
    apply Fin.ext
    change (0 + k.val) % m = k.val
    rw [zero_add, Nat.mod_eq_of_lt k.isLt]

/-- At most `m * 3 ^ (m-1)` directed circuits of length `m`, counted up to their starting edge,
meet one of the first `m/2` sides across the positive ray. Final draft, Lemma `lem:contour`, count clause. -/
theorem exists_finset_square_circuits_hitting_ray (z : Lattice) (m : ℕ) :
    ∃ C : Finset (Cycle (Lattice × Lattice)),
      (∀ c, c ∈ C ↔ ∃ v : Fin (m + 1) → Lattice,
        IsSquareCircuit v ∧ SquareCircuitHitsRay z v ∧ squareCircuitCycle v = c) ∧
      C.card ≤ m * 3 ^ (m - 1) := by
  classical
  by_cases hm : 0 < m
  · let T : Finset (ℕ × Bool) := (Finset.Icc 1 (m / 2)).product Finset.univ
    let e (p : ℕ × Bool) := if p.2 then squareCircuitRayEdge z p.1
      else (squareCircuitRayEdge z p.1).swap
    choose W hW hcard using fun p => exists_finset_walks_first_edge m hm (e p)
    let D (p : ℕ × Bool) := ((W p).filter IsSquareCircuit).image squareCircuitCycle
    refine ⟨T.biUnion D, ?_, ?_⟩
    · intro c
      constructor
      · intro hc
        obtain ⟨p, hp, hpc⟩ := Finset.mem_biUnion.mp hc
        obtain ⟨v, hv, hvc⟩ := Finset.mem_image.mp hpc
        have hvW := (hW p v).mp (Finset.mem_filter.mp hv).1
        have hp' := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
        refine ⟨v, (Finset.mem_filter.mp hv).2, ⟨p.1, hp'.1, hp'.2, ⟨0, hm⟩, ?_⟩, hvc⟩
        by_cases hb : p.2 = true
        · exact Or.inl (by simpa [e, hb] using hvW.1)
        · exact Or.inr (by simpa [e, hb] using hvW.1)
      · rintro ⟨v, hv, ⟨j, hj₁, hj₂, i, hi⟩, hvc⟩
        obtain ⟨w, hw, hw₀, hwc⟩ := exists_circuit_starting_at_edge hv i
        have hmem (p : ℕ × Bool) (hp : p.1 = j) (hfirst : squareCircuitEdge w ⟨0, hm⟩ = e p) :
            c ∈ T.biUnion D := by
          refine Finset.mem_biUnion.mpr ⟨p, ?_, Finset.mem_image.mpr ⟨w, ?_, hwc.trans hvc⟩⟩
          · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp.symm ▸ hj₁, hp.symm ▸ hj₂⟩,
              Finset.mem_univ _⟩
          · exact Finset.mem_filter.mpr ⟨(hW p w).mpr ⟨hfirst, hw.2.1, circuit_no_return hw⟩, hw⟩
        rcases hi with hi | hi
        · exact hmem (j, true) rfl (hw₀.trans hi)
        · exact hmem (j, false) rfl (hw₀.trans hi)
    · apply (Finset.card_biUnion_le).trans
      calc
        ∑ p ∈ T, (D p).card ≤ ∑ _p ∈ T, 3 ^ (m - 1) := by
          apply Finset.sum_le_sum
          intro p _
          exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (hcard p))
        _ = T.card * 3 ^ (m - 1) := Finset.sum_const_nat (fun _ _ => rfl)
        _ ≤ m * 3 ^ (m - 1) := by
          apply Nat.mul_le_mul_right
          change ((Finset.Icc 1 (m / 2)).product (Finset.univ : Finset Bool)).card ≤ m
          rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
            Fintype.card_bool, Nat.card_Icc]
          omega
  · refine ⟨∅, ?_, by simp⟩
    intro c
    simp only [Finset.notMem_empty, false_iff]
    rintro ⟨v, _, ⟨j, hj₁, hj₂, _, _⟩, _⟩
    omega

end LPPDifferentiability
