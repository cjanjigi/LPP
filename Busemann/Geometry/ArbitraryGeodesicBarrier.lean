/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
import LPP_Foundations.Model.Paths.HeightOrder

@[expose] public section
open Filter LPPDifferentiability

namespace LPP.Busemann

/-- An ordinary maximizing ray frequently strictly northwest of a same-root
locally-rightmost barrier stays northwest at every shared absolute level.
Only the barrier has greatest maximizing segments. This is the reflected
one-sided comparison used in JSP (2025), Lemma 5.1; it asserts no axis
classification or probability-event conclusion. -/
theorem pathSoutheastLE_of_frequently_lt_locallyRightmostGeodesic
    (ω : LPPDifferentiability.Environment) (u : Lattice)
    (γ ρ : ℕ → Lattice)
    (hstart : γ 0 = u)
    (hsteps : ∀ n : ℕ,
      γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
        γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ)))
    (hsegments : LPPDifferentiability.has_maximizing_segments ω γ)
    (hbarrier : IsLocallyRightmostGeodesic ω u ρ)
    (hgap : ∃ᶠ n : ℕ in atTop, (γ n).1 < (ρ n).1) :
    pathSoutheastLE γ ρ := by
  rcases hbarrier with ⟨hρstart, hρsteps, hρsegments⟩

  -- Each unit step raises the absolute level by one.
  have hγlevel : ∀ n : ℕ,
      (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) := by
    intro n
    induction n with
    | zero => simp [hstart]
    | succ n ih =>
        rcases hsteps n with h | h <;>
          simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega
  have hρlevel : ∀ n : ℕ,
      (ρ n).1 + (ρ n).2 = u.1 + u.2 + (n : ℤ) := by
    intro n
    induction n with
    | zero => simp [hρstart]
    | succ n ih =>
        rcases hρsteps n with h | h <;>
          simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega

  -- A strict eastward error is contradicted by a later reversed comparison.
  have hfirst (a : ℕ) : (γ a).1 ≤ (ρ a).1 := by
    by_contra hnot
    have hbad : (ρ a).1 < (γ a).1 := by omega
    obtain ⟨b, hab, hgapb⟩ := (Filter.frequently_atTop'.1 hgap) a
    have hlevelA : (γ a).1 + (γ a).2 = (ρ a).1 + (ρ a).2 := by
      rw [hγlevel a, hρlevel a]
    have hlevelB : (γ b).1 + (γ b).2 = (ρ b).1 + (ρ b).2 := by
      rw [hγlevel b, hρlevel b]
    have hheightA : (γ a).2 < (ρ a).2 := by omega
    have hheightB : (ρ b).2 < (γ b).2 := by omega

    let p : ℕ → Lattice := fun k => γ (a + k)
    let q : ℕ → Lattice := fun k => ρ (a + k)

    -- The reversed endpoint heights force the tails to meet.
    have hpsteps : ∀ k : ℕ,
        p (k + 1) = p k + ((1 : ℤ), (0 : ℤ)) ∨
          p (k + 1) = p k + ((0 : ℤ), (1 : ℤ)) := by
      intro k
      simpa only [p, Nat.add_succ] using hsteps (a + k)
    have hqsteps : ∀ k : ℕ,
        q (k + 1) = q k + ((1 : ℤ), (0 : ℤ)) ∨
          q (k + 1) = q k + ((0 : ℤ), (1 : ℤ)) := by
      intro k
      simpa only [q, Nat.add_succ] using hρsteps (a + k)
    have hpqlevel : (p 0).1 + (p 0).2 = (q 0).1 + (q 0).2 := by
      simpa only [p, q, Nat.add_zero] using hlevelA

    let N : ℕ := b - a
    have hAN : a + N = b := by
      dsimp [N]
      omega
    have hfinalHeight : (q N).2 < (p N).2 := by
      change (ρ (a + N)).2 < (γ (a + N)).2
      rw [hAN]
      exact hheightB
    have hmeet : ∃ k : ℕ, k ≤ N ∧ p k = q k := by
      by_contra hno
      have hAvoid : ∀ k : ℕ, k ≤ N → p k ≠ q k := by
        intro k hk heq
        exact hno ⟨k, hk, heq⟩
      have hstartHeight : (p 0).2 < (q 0).2 := by
        simpa only [p, q, Nat.add_zero] using hheightA
      have hpreserved :=
        (LPPDifferentiability.up_right_paths_strict_height_order_iff_of_disjoint
          p q N hpsteps hqsteps hpqlevel hAvoid).mp hstartHeight
      omega

    obtain ⟨k, _, hmeetTails⟩ := hmeet
    have hkpos : 0 < k := by
      by_contra hknot
      have hkzero : k = 0 := by omega
      have hsame : γ a = ρ a := by
        simpa [p, q, hkzero] using hmeetTails
      have hfirstEq : (γ a).1 = (ρ a).1 := congrArg Prod.fst hsame
      omega
    let T : ℕ := a + k
    have hTpos : 0 < T := by
      dsimp [T]
      omega
    have hmeetAtT : γ T = ρ T := by
      simpa [T, p, q] using hmeetTails

    -- Compare actual root-to-meeting-point maximizing prefixes.
    obtain ⟨dγ, pγ, hlenγ, hverticesγ, hweightγ⟩ := hsegments 0 T hTpos
    obtain ⟨dρ, pρ, hlenρ, hverticesρ, hweightρ, hgreatρ⟩ :=
      hρsegments 0 T hTpos
    have hγend : pγ.vertex (Fin.last (dγ.1 + dγ.2)) = γ T := by
      simpa [hlenγ] using hverticesγ (Fin.last (dγ.1 + dγ.2))
    have hρend : pρ.vertex (Fin.last (dρ.1 + dρ.2)) = ρ T := by
      simpa [hlenρ] using hverticesρ (Fin.last (dρ.1 + dρ.2))
    have hdisplacement :
        u + ((dγ.1 : ℤ), (dγ.2 : ℤ)) = u + ((dρ.1 : ℤ), (dρ.2 : ℤ)) := by
      calc
        u + ((dγ.1 : ℤ), (dγ.2 : ℤ)) =
            pγ.vertex (Fin.last (dγ.1 + dγ.2)) := by
          simpa [hstart] using pγ.finish.symm
        _ = γ T := hγend
        _ = ρ T := hmeetAtT
        _ = pρ.vertex (Fin.last (dρ.1 + dρ.2)) := hρend.symm
        _ = u + ((dρ.1 : ℤ), (dρ.2 : ℤ)) := by
          simpa [hρstart] using pρ.finish
    have hd1 : dγ.1 = dρ.1 := by
      apply Int.ofNat.inj
      have hfst := congrArg Prod.fst hdisplacement
      simp only [Prod.fst_add] at hfst
      exact add_left_cancel hfst
    have hd2 : dγ.2 = dρ.2 := by
      apply Int.ofNat.inj
      have hsnd := congrArg Prod.snd hdisplacement
      simp only [Prod.snd_add] at hsnd
      exact add_left_cancel hsnd
    have hd : dγ = dρ := Prod.ext hd1 hd2
    cases hd

    have hweightγρ : pathWeight ω pγ = lastPassage ω (ρ 0) dγ := by
      simpa [hstart, hρstart] using hweightγ
    let hγasρ : LPPDifferentiability.Path (ρ 0) dγ :=
      { vertex := pγ.vertex
        start := by
          rw [pγ.start, hstart, hρstart]
        finish := by
          simpa [hstart, hρstart] using pγ.finish
        step := pγ.step }
    have hweightAsρ : pathWeight ω hγasρ = lastPassage ω (ρ 0) dγ := by
      simpa only [pathWeight, hγasρ] using hweightγρ
    have hgreatCompare := hgreatρ hγasρ hweightAsρ
    have haT : a < T := by
      dsimp [T]
      omega
    have hi : a < dγ.1 + dγ.2 + 1 := by
      rw [hlenγ]
      omega
    let i : Fin (dγ.1 + dγ.2 + 1) := ⟨a, hi⟩
    have hγatA : pγ.vertex i = γ a := by
      simpa [i] using hverticesγ i
    have hρatA : pρ.vertex i = ρ a := by
      simpa [i] using hverticesρ i
    have hgreatAtA := (hgreatCompare i).1
    have hfirstOrder : (γ a).1 ≤ (ρ a).1 := by
      change (pγ.vertex i).1 ≤ (pρ.vertex i).1 at hgreatAtA
      simpa only [hγatA, hρatA] using hgreatAtA
    exact (not_le_of_gt hbad) hfirstOrder

  -- Reduce the shared absolute level condition to equal local times.
  intro m n hshared
  have htimesCast : (m : ℤ) = (n : ℤ) := by
    rw [hstart, hρstart] at hshared
    exact add_left_cancel hshared
  have htimes : m = n := Int.ofNat.inj htimesCast
  subst n
  constructor
  · exact hfirst m
  · have hγlevelM := hγlevel m
    have hρlevelM := hρlevel m
    have hfirstM : (γ m).1 ≤ (ρ m).1 := hfirst m
    omega

end LPP.Busemann
