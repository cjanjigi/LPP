/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.PathWeight
import LPP_Foundations.Model.Paths.Split
import LPP_Foundations.Model.Paths.Translate
import LPP_Foundations.Model.Paths.HorizontalFirst
import Mathlib.Tactic.Convert
import Mathlib.Tactic.SplitIfs

/-! Intrinsic head-step and suffix equivalence for actual up-right paths.
This supplies finite-path geometry for JR1810.03580v3, Section 2.2 and Appendix A.1.
Weights include the starting site and omit the terminal site. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

private def castPath {x y : Lattice} {d e : ℕ × ℕ}
    (hx : x = y) (hd : d = e) (p : Path x d) : Path y e := by
  subst y
  subst e
  exact p

private theorem castPath_vertex {x y : Lattice} {d e : ℕ × ℕ}
    (hx : x = y) (hd : d = e) (p : Path x d)
    (i : Fin (e.1 + e.2 + 1)) (j : Fin (d.1 + d.2 + 1))
    (hij : i.val = j.val) : (castPath hx hd p).vertex i = p.vertex j := by
  subst y
  subst e
  change p.vertex i = p.vertex j
  exact congrArg p.vertex (Fin.ext hij)

private def firstTime (s d : ℕ × ℕ) (hs : s.1 + s.2 = 1) :
    Fin ((s + d).1 + (s + d).2 + 1) :=
  ⟨1, by simp only [Prod.fst_add, Prod.snd_add]; omega⟩

private theorem split_first {x : Lattice} {s d : ℕ × ℕ}
    (hs : s.1 + s.2 = 1) (p : Path x (s + d))
    (hp : p.vertex (firstTime s d hs) = x + ((s.1 : ℤ), (s.2 : ℤ))) :
    p.splitDisplacement (firstTime s d hs) = s := by
  have h1 := p.splitDisplacement_fst_cast (firstTime s d hs)
  have h2 := p.splitDisplacement_snd_cast (firstTime s d hs)
  rw [hp] at h1 h2
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  apply Prod.ext <;> omega

private def dropFirst {x : Lattice} {s d : ℕ × ℕ}
    (hs : s.1 + s.2 = 1) (p : Path x (s + d))
    (hp : p.vertex (firstTime s d hs) = x + ((s.1 : ℤ), (s.2 : ℤ))) :
    Path (x + ((s.1 : ℤ), (s.2 : ℤ))) d :=
  castPath hp (by
    rw [split_first hs p hp]
    exact Prod.ext (Nat.add_sub_cancel_left s.1 d.1)
      (Nat.add_sub_cancel_left s.2 d.2))
    (p.suffix (firstTime s d hs))

private theorem dropFirst_vertex {x : Lattice} {s d : ℕ × ℕ}
    (hs : s.1 + s.2 = 1) (p : Path x (s + d))
    (hp : p.vertex (firstTime s d hs) = x + ((s.1 : ℤ), (s.2 : ℤ)))
    (i : Fin (d.1 + d.2 + 1)) :
    (dropFirst hs p hp).vertex i = p.vertex ⟨1 + i.val, by
      have hi := i.isLt
      simp only [Prod.fst_add, Prod.snd_add]
      omega⟩ := by
  unfold dropFirst
  exact castPath_vertex hp _ (p.suffix (firstTime s d hs)) i
    ⟨i.val, by
      have hl := p.suffix_length (firstTime s d hs)
      have hi := i.isLt
      simp only [Prod.fst_add, Prod.snd_add] at hl
      change _ = (s.1 + d.1 + (s.2 + d.2)) - 1 at hl
      omega⟩ rfl

private theorem concat_first {x : Lattice} {s d : ℕ × ℕ}
    (hs : s.1 + s.2 = 1) (q : Path (x + ((s.1 : ℤ), (s.2 : ℤ))) d) :
    ((horizontalFirst x s).concat q).vertex (firstTime s d hs) =
      x + ((s.1 : ℤ), (s.2 : ℤ)) := by
  have hv := Path.concat_vertex_left (horizontalFirst x s) q (Fin.last (s.1 + s.2))
  have hi : (⟨(Fin.last (s.1 + s.2)).val, by
      have hi := (Fin.last (s.1 + s.2)).isLt
      simp only [Prod.fst_add, Prod.snd_add]
      omega⟩ : Fin ((s + d).1 + (s + d).2 + 1)) = firstTime s d hs := by
    apply Fin.ext
    exact hs
  rw [hi] at hv
  exact hv.trans (horizontalFirst x s).finish

private theorem dropFirst_concat {x : Lattice} {s d : ℕ × ℕ}
    (hs : s.1 + s.2 = 1) (q : Path (x + ((s.1 : ℤ), (s.2 : ℤ))) d) :
    dropFirst hs ((horizontalFirst x s).concat q) (concat_first hs q) = q := by
  apply LPPDifferentiability.Path.ext
  intro i
  rw [dropFirst_vertex]
  have hv := Path.concat_vertex_right (horizontalFirst x s) q i
  convert hv using 1
  congr 1
  apply Fin.ext
  change 1 + i.val = s.1 + s.2 + i.val
  omega

private theorem concat_dropFirst {x : Lattice} {s d : ℕ × ℕ}
    (hs : s.1 + s.2 = 1) (p : Path x (s + d))
    (hp : p.vertex (firstTime s d hs) = x + ((s.1 : ℤ), (s.2 : ℤ))) :
    (horizontalFirst x s).concat (dropFirst hs p hp) = p := by
  apply LPPDifferentiability.Path.ext
  intro i
  change Path.concatVertex _ _ i = _
  unfold Path.concatVertex
  split_ifs with hi
  · have hi0 : i.val = 0 := by omega
    have hleft : (⟨i.val, by omega⟩ : Fin (s.1 + s.2 + 1)) = 0 := Fin.ext hi0
    rw [hleft, (horizontalFirst x s).start]
    have hright : i = 0 := Fin.ext hi0
    rw [hright, p.start]
  · rw [dropFirst_vertex]
    congr 1
    apply Fin.ext
    change 1 + (i.val - (s.1 + s.2)) = i.val
    omega

private def firstStepEquiv (x : Lattice) (s d : ℕ × ℕ) (hs : s.1 + s.2 = 1) :
    {p : Path x (s + d) //
      p.vertex (firstTime s d hs) = x + ((s.1 : ℤ), (s.2 : ℤ))} ≃
      Path (x + ((s.1 : ℤ), (s.2 : ℤ))) d where
  toFun p := dropFirst hs p.val p.property
  invFun q := ⟨(horizontalFirst x s).concat q, concat_first hs q⟩
  left_inv p := Subtype.ext (concat_dropFirst hs p.val p.property)
  right_inv q := dropFirst_concat hs q

private theorem unit_pathWeight (ω : Environment) (x : Lattice) (s : ℕ × ℕ)
    (hs : s.1 + s.2 = 1) : pathWeight ω (horizontalFirst x s) = ω x := by
  unfold pathWeight
  calc
    (∑ i : Fin (s.1 + s.2), ω ((horizontalFirst x s).vertex i.castSucc)) =
        ∑ _i : Fin (s.1 + s.2), ω x := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : i.castSucc = 0 := by
        apply Fin.ext
        have hi := i.isLt
        change i.val = 0
        omega
      rw [hi, (horizontalFirst x s).start]
    _ = ω x := by simp [hs]

private theorem firstStepEquiv_weight (ω : Environment) (x : Lattice)
    (s d : ℕ × ℕ) (hs : s.1 + s.2 = 1)
    (p : {p : Path x (s + d) //
      p.vertex (firstTime s d hs) = x + ((s.1 : ℤ), (s.2 : ℤ))}) :
    pathWeight ω p.val = ω x + pathWeight ω (firstStepEquiv x s d hs p) := by
  calc
    pathWeight ω p.val = pathWeight ω ((horizontalFirst x s).concat
        (dropFirst hs p.val p.property)) :=
      congrArg (pathWeight ω) (concat_dropFirst hs p.val p.property).symm
    _ = ω x + pathWeight ω (firstStepEquiv x s d hs p) := by
      rw [pathWeight_concat, unit_pathWeight ω x s hs]
      rfl

/-- Removing a specified unit first step is a bijection on actual paths.
Every child vertex is the corresponding original vertex one time later, and
terminal-excluded weight splits off the starting weight. This is the intrinsic
finite-path decomposition used in JR1810.03580v3, Section 2.2 and Appendix A.1. -/
theorem Path.exists_first_step_equiv (x : Lattice) (s d : ℕ × ℕ)
    (hs : s.1 + s.2 = 1) :
    ∃ e : {p : Path x (s + d) //
        p.vertex ⟨1, by simp only [Prod.fst_add, Prod.snd_add]; omega⟩ =
          x + ((s.1 : ℤ), (s.2 : ℤ))} ≃
        Path (x + ((s.1 : ℤ), (s.2 : ℤ))) d,
      (∀ p (i : Fin (d.1 + d.2 + 1)),
        (e p).vertex i = p.val.vertex ⟨i.val + 1, by
          have hi := i.isLt
          simp only [Prod.fst_add, Prod.snd_add]
          omega⟩) ∧
      (∀ (ω : Environment) p,
        pathWeight ω p.val = ω x + pathWeight ω (e p)) := by
  refine ⟨firstStepEquiv x s d hs, ?_, ?_⟩
  · intro p i
    change (dropFirst hs p.val p.property).vertex i = _
    have hv := dropFirst_vertex hs p.val p.property i
    refine hv.trans ?_
    congr 1
    apply Fin.ext
    exact Nat.add_comm 1 i.val
  · intro ω p
    exact firstStepEquiv_weight ω x s d hs p

end LPPDifferentiability
