/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.ExcessBlockGeometry
import Mathlib.Tactic

/-! Closed translated boxes are disjoint on the forty signed residue classes. -/
public section
namespace LPPDifferentiability

/-- The source gaps 4 and 10 separate the literal closed translated boxes. -/
theorem excess_blocks_disjoint (a s : ℝ) (m : ℕ) (Q : Finset Lattice)
    (hQ : ∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
      |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1)
    (hs : 3 ≤ s) (hm : 1 ≤ m) (b c : ℤ × ℤ)
    (hsep : 4 ≤ |b.1-c.1| ∨ 10 ≤ |b.2-c.2|) :
    let v : ℤ × ℤ → Lattice := fun d =>
      let j : ℤ := ⌊(d.2:ℝ)*s+a*((d.1*m:ℤ):ℝ)⌋
      (j,d.1*m-j)
    Disjoint (Q.map ⟨fun w => v b+w, fun _ _ h => add_left_cancel h⟩)
      (Q.map ⟨fun w => v c+w, fun _ _ h => add_left_cancel h⟩) := by
  dsimp only
  apply Finset.disjoint_left.mpr
  intro z hzb hzc
  rw [mem_translated_excess_block a s m Q hQ] at hzb hzc
  obtain ⟨hb,hblo,hbhi⟩ := excess_block_center a s m b.1 b.2
  obtain ⟨hc,hclo,hchi⟩ := excess_block_center a s m c.1 c.2
  rw [hb] at hzb
  rw [hc] at hzc
  rcases hsep with hp | hh
  · rcases le_abs.mp hp with hp | hp
    · nlinarith only [hzb.1,hzc.2.1,hp, (show (1:ℤ) ≤ m by exact_mod_cast hm)]
    · nlinarith only [hzc.1,hzb.2.1,hp, (show (1:ℤ) ≤ m by exact_mod_cast hm)]
  · rcases abs_le.mp hzb.2.2 with ⟨hzbl,hzbu⟩
    rcases abs_le.mp hzc.2.2 with ⟨hzcl,hzcu⟩
    rcases le_abs.mp hh with hh | hh
    · have hhR : 10 ≤ (b.2:ℝ)-(c.2:ℝ) := by exact_mod_cast hh
      nlinarith only [hhR,hs,hblo,hchi,hzbl,hzcu]
    · have hhR : 10 ≤ -((b.2:ℝ)-(c.2:ℝ)) := by exact_mod_cast hh
      nlinarith only [hhR,hs,hclo,hbhi,hzcl,hzbu]

/-- Genuine signed congruences force one of the two separation gaps. -/
theorem excess_residue_separation (b c : ℤ × ℤ)
    (hp : b.1 % 4 = c.1 % 4) (hh : b.2 % 10 = c.2 % 10)
    (hne : b ≠ c) : 4 ≤ |b.1-c.1| ∨ 10 ≤ |b.2-c.2| := by
  by_contra h
  push Not at h
  have hpbound := abs_lt.mp h.1
  have hhbound := abs_lt.mp h.2
  have hp' : b.1=c.1 := by omega
  have hh' : b.2=c.2 := by omega
  exact hne (Prod.ext hp' hh')

/-- Every signed index belongs to exactly one of the forty classes. -/
theorem excess_residue_partition (b : ℤ × ℤ) :
    ∃! r : Fin 4 × Fin 10,
      b.1 % 4 = (r.1.val:ℤ) ∧ b.2 % 10 = (r.2.val:ℤ) := by
  let α : Fin 4 := ⟨(b.1%4).toNat, by omega⟩
  let β : Fin 10 := ⟨(b.2%10).toNat, by omega⟩
  refine ⟨(α,β), ⟨by dsimp [α]; omega, by dsimp [β]; omega⟩, ?_⟩
  intro r hr
  apply Prod.ext <;> apply Fin.ext
  · dsimp [α]
    omega
  · dsimp [β]
    omega

/-- The literal whole-class indexing includes all signed congruent indices. -/
theorem excess_residue_index_iff (α : Fin 4) (β : Fin 10) (b : ℤ × ℤ) :
    (b.1 % 4 = (α.val:ℤ) ∧ b.2 % 10 = (β.val:ℤ)) ↔
      ∃ v : ℤ × ℤ, b = (4*v.1+(α.val:ℤ),10*v.2+(β.val:ℤ)) := by
  have ha := α.isLt
  have hb := β.isLt
  constructor
  · intro h
    refine ⟨(b.1/4,b.2/10), ?_⟩
    apply Prod.ext <;> dsimp only <;> omega
  · rintro ⟨v,rfl⟩
    constructor <;> dsimp only <;> omega

/-- All boxes in a fixed literal residue class are pairwise disjoint. -/
theorem excess_residue_boxes_pairwise (a s : ℝ) (m : ℕ) (Q : Finset Lattice)
    (hQ : ∀ z, z ∈ Q ↔ 0 ≤ z.1+z.2 ∧ z.1+z.2 ≤ 3*(m:ℤ) ∧
      |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)| ≤ 4*s+1)
    (hs : 3 ≤ s) (hm : 1 ≤ m) (α : Fin 4) (β : Fin 10) :
    let v : ℤ × ℤ → Lattice := fun d =>
      let p := 4*d.1+(α.val:ℤ)
      let h := 10*d.2+(β.val:ℤ)
      let j : ℤ := ⌊(h:ℝ)*s+a*((p*m:ℤ):ℝ)⌋
      (j,p*m-j)
    Pairwise (fun b c : ℤ × ℤ =>
      Disjoint (Q.map ⟨fun w => v b+w, fun _ _ h => add_left_cancel h⟩)
        (Q.map ⟨fun w => v c+w, fun _ _ h => add_left_cancel h⟩)) := by
  dsimp only
  intro b c hne
  apply excess_blocks_disjoint a s m Q hQ hs hm
    (4*b.1+(α.val:ℤ),10*b.2+(β.val:ℤ))
    (4*c.1+(α.val:ℤ),10*c.2+(β.val:ℤ))
  apply excess_residue_separation
  · dsimp only
    omega
  · dsimp only
    omega
  · intro heq
    apply hne
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    apply Prod.ext <;> dsimp only at h1 h2 ⊢ <;> omega

end LPPDifferentiability
end
