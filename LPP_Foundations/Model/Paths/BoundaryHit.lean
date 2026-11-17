/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
import Lean.Elab.Tactic.Omega

/-! Finite crossing and boundary geometry for up-right lattice paths. -/

@[expose] public section

namespace LPPDifferentiability

/-- Two up-right paths with opposite first steps either meet again or the
second reaches the first path's northern boundary to the left of its endpoint.
This is the finite path geometry used in GRS, Appendix A, proof of A.5. -/
theorem up_right_paths_meet_or_hit_north
    (x : Lattice) (p q : ℕ → Lattice) (N : ℕ) (M1 M2 : ℤ)
    (hp0 : p 0 = x) (hq0 : q 0 = x)
    (hp : ∀ n, p (n + 1) = p n + (1, 0) ∨ p (n + 1) = p n + (0, 1))
    (hq : ∀ n, q (n + 1) = q n + (1, 0) ∨ q (n + 1) = q n + (0, 1))
    (hfirstp : p 1 = x + (1, 0)) (hfirstq : q 1 = x + (0, 1))
    (hbelow : x.2 < M2) (hend : p N = (M1, M2)) :
    ∃ k : ℕ, 0 < k ∧ k ≤ N ∧
      (p k = q k ∨ (q k).2 = M2 ∧ (q k).1 ≤ M1) := by
  -- Both paths lie on the same diagonal at each time.
  have hlevel (r : ℕ → Lattice) (hr0 : r 0 = x)
      (hr : ∀ n, r (n + 1) = r n + (1, 0) ∨ r (n + 1) = r n + (0, 1)) :
      ∀ n, (r n).1 + (r n).2 = x.1 + x.2 + (n : ℤ) := by
    intro n
    induction n with
    | zero => simp only [hr0, Nat.cast_zero, add_zero]
    | succ n ih =>
        rcases hr n with h | h <;>
          simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega
  have hplevel := hlevel p hp0 hp
  have hqlevel := hlevel q hq0 hq
  have hN : 0 < N := by
    by_contra hn
    have : N = 0 := by omega
    subst N
    rw [hp0] at hend
    have := congrArg Prod.snd hend
    simp only at this
    omega
  -- Stop at the first time q reaches the boundary or its height is no
  -- greater than p's height. Such a time exists by N.
  have hex : ∃ k : ℕ, 0 < k ∧ (M2 ≤ (q k).2 ∨ (q k).2 ≤ (p k).2) := by
    refine ⟨N, hN, ?_⟩
    have he : (p N).2 = M2 := congrArg Prod.snd hend
    omega
  let k := Nat.find hex
  have hk : 0 < k ∧ (M2 ≤ (q k).2 ∨ (q k).2 ≤ (p k).2) := Nat.find_spec hex
  have hkN : k ≤ N := by
    apply Nat.find_min' hex
    refine ⟨hN, ?_⟩
    have he : (p N).2 = M2 := congrArg Prod.snd hend
    omega
  have hstepq (n : ℕ) : (q n).2 ≤ (q (n + 1)).2 ∧
      (q (n + 1)).2 ≤ (q n).2 + 1 := by
    rcases hq n with h | h <;> simp only [h, Prod.snd_add] <;> omega
  have hstepp (n : ℕ) : (p n).2 ≤ (p (n + 1)).2 ∧
      (p (n + 1)).2 ≤ (p n).2 + 1 := by
    rcases hp n with h | h <;> simp only [h, Prod.snd_add] <;> omega
  have hfirstgap : (q 1).2 = x.2 + 1 ∧ (p 1).2 = x.2 := by
    simp only [hfirstp, hfirstq, Prod.snd_add, add_zero, and_self]
  have hprevious : k = 1 ∨ ((q (k - 1)).2 < M2 ∧
      (p (k - 1)).2 < (q (k - 1)).2) := by
    by_cases hone : k = 1
    · exact Or.inl hone
    · right
      have hlt : k - 1 < k := by omega
      have hn := Nat.find_min hex hlt
      have hp : 0 < k - 1 := by omega
      have : ¬ (M2 ≤ (q (k - 1)).2 ∨ (q (k - 1)).2 ≤ (p (k - 1)).2) := by
        intro h
        exact hn ⟨hp, h⟩
      omega
  have hstepqk : (q (k - 1)).2 ≤ (q k).2 ∧
      (q k).2 ≤ (q (k - 1)).2 + 1 := by
    have hs := hstepq (k - 1)
    have : k - 1 + 1 = k := by omega
    simpa only [this] using hs
  have hsteppk : (p (k - 1)).2 ≤ (p k).2 ∧
      (p k).2 ≤ (p (k - 1)).2 + 1 := by
    have hs := hstepp (k - 1)
    have : k - 1 + 1 = k := by omega
    simpa only [this] using hs
  have hboundary_or_equal : (q k).2 = M2 ∨ (q k).2 = (p k).2 := by
    rcases hprevious with hone | hprev
    · have hqone : (q k).2 = x.2 + 1 := by rw [hone]; exact hfirstgap.1
      have hpone : (p k).2 = x.2 := by rw [hone]; exact hfirstgap.2
      rcases hk.2 with hb | hg
      · left; omega
      · omega
    · rcases hk.2 with hb | hg
      · left; omega
      · right; omega
  refine ⟨k, hk.1, hkN, ?_⟩
  rcases hboundary_or_equal with hb | heq
  · right
    refine ⟨hb, ?_⟩
    have hpN := hplevel N
    have hqk := hqlevel k
    rw [hend] at hpN
    simp only at hpN
    omega
  · left
    apply Prod.ext
    · have hpK := hplevel k
      have hqK := hqlevel k
      omega
    · exact heq.symm

/-- The corresponding eastern boundary statement follows by interchanging the
coordinates in the finite geometry of GRS, Appendix A, proof of A.5. -/
theorem up_right_paths_meet_or_hit_east
    (x : Lattice) (p q : ℕ → Lattice) (N : ℕ) (M1 H : ℤ)
    (hp0 : p 0 = x) (hq0 : q 0 = x)
    (hp : ∀ n, p (n + 1) = p n + (1, 0) ∨ p (n + 1) = p n + (0, 1))
    (hq : ∀ n, q (n + 1) = q n + (1, 0) ∨ q (n + 1) = q n + (0, 1))
    (hfirstp : p 1 = x + (0, 1)) (hfirstq : q 1 = x + (1, 0))
    (hleft : x.1 < M1) (hend : p N = (M1, H)) :
    ∃ k : ℕ, 0 < k ∧ k ≤ N ∧
      (p k = q k ∨ (q k).1 = M1 ∧ (q k).2 ≤ H) := by
  let swap : Lattice → Lattice := fun z => (z.2, z.1)
  have hs0 : swap (p 0) = swap x := congrArg swap hp0
  have ht0 : swap (q 0) = swap x := congrArg swap hq0
  have hs : ∀ n, swap (p (n + 1)) = swap (p n) + (1, 0) ∨
      swap (p (n + 1)) = swap (p n) + (0, 1) := by
    intro n
    rcases hp n with h | h <;> simp only [h, swap, Prod.fst_add, Prod.snd_add] <;> simp
  have ht : ∀ n, swap (q (n + 1)) = swap (q n) + (1, 0) ∨
      swap (q (n + 1)) = swap (q n) + (0, 1) := by
    intro n
    rcases hq n with h | h <;> simp only [h, swap, Prod.fst_add, Prod.snd_add] <;> simp
  have hsfirst : swap (p 1) = swap x + (1, 0) := by
    simp [hfirstp, swap]
  have htfirst : swap (q 1) = swap x + (0, 1) := by
    simp [hfirstq, swap]
  have hsend : swap (p N) = (H, M1) := by simp [hend, swap]
  obtain ⟨k, hk, hkN, h⟩ := up_right_paths_meet_or_hit_north
    (swap x) (fun n => swap (p n)) (fun n => swap (q n)) N H M1
    hs0 ht0 hs ht hsfirst htfirst hleft hsend
  refine ⟨k, hk, hkN, ?_⟩
  rcases h with h | h
  · left
    apply Prod.ext
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h
  · exact Or.inr h

end LPPDifferentiability

end
