/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Path
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
import LPP_Foundations.Model.Paths.Geometry
import LPP_Foundations.Model.Paths.HorizontalFirst
import LPP_Foundations.Model.Paths.Level
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Reachable points on a later level

For a signed lattice point and a fixed number of directed steps, the possible
endpoints form a finite closed interval on the later level. The same description
holds in reverse for starting points that can reach a fixed endpoint.

The transverse coordinate is written inline as `(1 - a) * z.1 - a * z.2`.
The deterministic formulas hold for every real `a`.
-/

@[expose] public section

namespace LPPDifferentiability

/-- Forward endpoints after exactly `m` steps are indexed without repetition by
`Fin (m + 1)`, and are exactly the signed points above `u` on level `level(u)+m`. -/
theorem forwardReachable_mem_iff (u v : Lattice) (m : ℕ) :
    let endpoints : Finset Lattice :=
      Finset.univ.image (fun j : Fin (m + 1) =>
        u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))
    v ∈ endpoints ↔ u ≤ v ∧ v.1 + v.2 = u.1 + u.2 + (m : ℤ) := by
  classical
  change v ∈ Finset.univ.image (fun j : Fin (m + 1) =>
    u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) ↔ _
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨j, -, hj⟩
    have hjle : j.val ≤ m := by omega
    constructor
    · rw [← hj]
      change u.1 ≤ _ ∧ u.2 ≤ _
      simp only [Prod.fst_add, Prod.snd_add]
      constructor <;> omega
    · rw [← hj]
      simp only [Prod.fst_add, Prod.snd_add]
      omega
  · rintro ⟨hle, hlevel⟩
    change u.1 ≤ v.1 ∧ u.2 ≤ v.2 at hle
    rcases hle with ⟨h₁, h₂⟩
    have hd₁ : 0 ≤ v.1 - u.1 := by omega
    have hcast : ((v.1 - u.1).toNat : ℤ) = v.1 - u.1 :=
      Int.toNat_of_nonneg hd₁
    have hsum : (v.1 - u.1) + (v.2 - u.2) = (m : ℤ) := by omega
    have hjle : (v.1 - u.1).toNat ≤ m := by
      have hleZ : ((v.1 - u.1).toNat : ℤ) ≤ (m : ℤ) := by
        rw [hcast]
        omega
      exact_mod_cast hleZ
    let j : Fin (m + 1) := ⟨(v.1 - u.1).toNat, by omega⟩
    have hj₁ : (j.val : ℤ) = v.1 - u.1 := by
      change ((v.1 - u.1).toNat : ℤ) = _
      exact hcast
    have hj₂ : ((m - j.val : ℕ) : ℤ) = v.2 - u.2 := by
      omega
    have hpoint : v = u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)) := by
      apply Prod.ext
      · simp only [Prod.fst_add]
        omega
      · simp only [Prod.snd_add]
        omega
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ _, hpoint.symm⟩

/-- The forward endpoint enumeration has exactly `m + 1` distinct points. -/
theorem forwardReachable_card (u : Lattice) (m : ℕ) :
    let endpoints : Finset Lattice :=
      Finset.univ.image (fun j : Fin (m + 1) =>
        u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))
    endpoints.card = m + 1 := by
  classical
  change (Finset.univ.image (fun j : Fin (m + 1) =>
    u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))).card = m + 1
  have hinj : Function.Injective (fun j : Fin (m + 1) =>
      u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) := by
    intro i j hij
    apply Fin.ext
    have hfst := congrArg Prod.fst hij
    simp only [Prod.fst_add] at hfst
    omega
  rw [Finset.card_image_of_injective Finset.univ hinj]
  simp

/-- The transverse coordinate of a forward endpoint, with no restriction on
the real parameter `a`. -/
theorem forwardReachable_transverse (u : Lattice) (m : ℕ)
    (j : Fin (m + 1)) (a : ℝ) :
    (1 - a) * (((u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))).1 : ℤ) : ℝ) -
        a * (((u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))).2 : ℤ) : ℝ) =
      ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) - a * (m : ℝ) + (j.val : ℝ) := by
  have hj : j.val ≤ m := by omega
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_natCast,
    Nat.cast_sub hj]
  push_cast
  ring

/-- On the later level, coordinatewise reachability is equivalent to the
closed transverse interval from the first vertical to the first horizontal
endpoint. -/
theorem forwardLevelInterval_iff (u v : Lattice) (m : ℕ) (a : ℝ) :
    (u ≤ v ∧ v.1 + v.2 = u.1 + u.2 + (m : ℤ)) ↔
      (v.1 + v.2 = u.1 + u.2 + (m : ℤ) ∧
        ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ)) ∈
          Set.Icc ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - a * (m : ℝ))
            ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) + (1 - a) * (m : ℝ))) := by
  have hformula (hlevel : v.1 + v.2 = u.1 + u.2 + (m : ℤ)) :
      (1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) =
        ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) - a * (m : ℝ) +
          ((v.1 : ℝ) - (u.1 : ℝ)) := by
    have hlevelR : (v.1 : ℝ) + (v.2 : ℝ) =
        (u.1 : ℝ) + (u.2 : ℝ) + (m : ℝ) := by
      exact_mod_cast hlevel
    have hv₂ : (v.2 : ℝ) = (u.1 : ℝ) + (u.2 : ℝ) + (m : ℝ) - (v.1 : ℝ) := by
      linarith [hlevelR]
    rw [hv₂]
    ring
  constructor
  · rintro ⟨hle, hlevel⟩
    change u.1 ≤ v.1 ∧ u.2 ≤ v.2 at hle
    rcases hle with ⟨h₁, h₂⟩
    have hlevelR : (v.1 : ℝ) + (v.2 : ℝ) =
        (u.1 : ℝ) + (u.2 : ℝ) + (m : ℝ) := by
      exact_mod_cast hlevel
    have hd₁ : 0 ≤ (v.1 : ℝ) - (u.1 : ℝ) := by exact_mod_cast (sub_nonneg.mpr h₁)
    have hd₂ : 0 ≤ (v.2 : ℝ) - (u.2 : ℝ) := by exact_mod_cast (sub_nonneg.mpr h₂)
    have hsum : ((v.1 : ℝ) - (u.1 : ℝ)) +
        ((v.2 : ℝ) - (u.2 : ℝ)) = (m : ℝ) := by
      linarith [hlevelR]
    refine ⟨hlevel, ?_⟩
    rw [hformula hlevel]
    constructor <;> linarith
  · rintro ⟨hlevel, hinterval⟩
    have hlevelR : (v.1 : ℝ) + (v.2 : ℝ) =
        (u.1 : ℝ) + (u.2 : ℝ) + (m : ℝ) := by
      exact_mod_cast hlevel
    have hformula' := hformula hlevel
    have hd₁ : 0 ≤ (v.1 : ℝ) - (u.1 : ℝ) := by
      rw [hformula'] at hinterval
      linarith [hinterval.1]
    have hd₁m : (v.1 : ℝ) - (u.1 : ℝ) ≤ (m : ℝ) := by
      rw [hformula'] at hinterval
      linarith [hinterval.2]
    have h₁ : u.1 ≤ v.1 := by
      exact_mod_cast (show (u.1 : ℝ) ≤ (v.1 : ℝ) by linarith)
    have h₂ : u.2 ≤ v.2 := by
      have h₂R : (u.2 : ℝ) ≤ (v.2 : ℝ) := by linarith [hlevelR, hd₁m]
      exact_mod_cast h₂R
    exact ⟨⟨h₁, h₂⟩, hlevel⟩

/-- Filtering the forward enumeration by its closed level interval retains all
of its `m + 1` points. -/
theorem forwardLevelInterval_card (u : Lattice) (m : ℕ) (a : ℝ) :
    let endpoints : Finset Lattice :=
      Finset.univ.image (fun j : Fin (m + 1) =>
        u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))
    (endpoints.filter (fun v =>
      v.1 + v.2 = u.1 + u.2 + (m : ℤ) ∧
        ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ)) ∈
          Set.Icc ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - a * (m : ℝ))
            ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) + (1 - a) * (m : ℝ)))).card =
      m + 1 := by
  classical
  change ((Finset.univ.image (fun j : Fin (m + 1) =>
    u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))).filter (fun v =>
      v.1 + v.2 = u.1 + u.2 + (m : ℤ) ∧
        ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ)) ∈
          Set.Icc ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - a * (m : ℝ))
            ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) + (1 - a) * (m : ℝ)))).card = m + 1
  have hfilter :
      ((Finset.univ.image (fun j : Fin (m + 1) =>
        u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))).filter (fun v =>
          v.1 + v.2 = u.1 + u.2 + (m : ℤ) ∧
            ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ)) ∈
              Set.Icc ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - a * (m : ℝ))
                ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) + (1 - a) * (m : ℝ)))) =
      Finset.univ.image (fun j : Fin (m + 1) =>
        u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact (forwardLevelInterval_iff u v m a).mp
      ((forwardReachable_mem_iff u v m).mp hv)
  rw [hfilter]
  exact forwardReachable_card u m

/-- Every point in the forward enumeration has an actual horizontal-first
path whose terminal vertex is that point. -/
theorem exists_path_to_forwardReachable (u : Lattice) (v : Lattice) (m : ℕ)
    (hv : v ∈ Finset.univ.image (fun j : Fin (m + 1) =>
      u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))) :
    ∃ j : Fin (m + 1), ∃ p : Path u (j.val, m - j.val),
      p.vertex (Fin.last (j.val + (m - j.val))) = v := by
  classical
  change v ∈ Finset.univ.image (fun j : Fin (m + 1) =>
    u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) at hv
  rcases Finset.mem_image.mp hv with ⟨j, -, hj⟩
  refine ⟨j, horizontalFirst u (j.val, m - j.val), ?_⟩
  rw [← hj]
  exact (horizontalFirst u (j.val, m - j.val)).finish

/-- An actual path of length `m` ends in the forward endpoint enumeration.
The lower and upper coordinate bounds come from its actual steps. -/
theorem Path.finish_mem_forwardReachable {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (m : ℕ) (hm : d.1 + d.2 = m) :
    p.vertex (Fin.last (d.1 + d.2)) ∈ Finset.univ.image (fun j : Fin (m + 1) =>
      u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) := by
  have hbox := Path.vertex_mem_Icc p (Fin.last (d.1 + d.2))
  have hle : u ≤ p.vertex (Fin.last (d.1 + d.2)) := hbox.1
  have hlevel := Path.level p (Fin.last (d.1 + d.2))
  simp only [Fin.val_last] at hlevel
  have hlevel' :
      (p.vertex (Fin.last (d.1 + d.2))).1 +
          (p.vertex (Fin.last (d.1 + d.2))).2 = u.1 + u.2 + (m : ℤ) := by
    rw [hlevel]
    have hmZ : ((d.1 + d.2 : ℕ) : ℤ) = (m : ℤ) := by exact_mod_cast hm
    omega
  exact (forwardReachable_mem_iff u _ m).2 ⟨hle, hlevel'⟩

end LPPDifferentiability
