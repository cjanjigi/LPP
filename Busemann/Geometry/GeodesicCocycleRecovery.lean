/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import LPP_Foundations.Model.Paths.UpRightRay
public import Busemann.Frozen.Definitions.Recovery
public import Mathlib.Topology.Instances.Real.Lemmas
import LPP_Foundations.Model.LastPassage.Outgoing
import LPP_Foundations.Model.LastPassage.OptimalSplit
import LPP_Foundations.Model.LastPassage.Inclusive
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Separation.Hausdorff

/-! Recovery and calibration from real passage limits along a geodesic. -/

@[expose] public section
open Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

private theorem int_toNat_sub_one (z : ℤ) (hz : 1 ≤ z) :
    (z - 1).toNat + 1 = z.toNat := by
  have hz₀ : 0 ≤ z := by omega
  have hz₁ : 0 ≤ z - 1 := by omega
  have hnat₀ := Int.toNat_of_nonneg hz₀
  have hnat₁ := Int.toNat_of_nonneg hz₁
  omega

/-- A real passage-limit field along an ordinary coordinate-escaping ray
recovers the environment and calibrates each actual ray edge. The field is
supplied by its complete passage-difference characterization; this theorem
asserts no existence, probability or additivity statement. Strong Existence, g400 recovery lines 1606–1611 and maximizing-ray decomposition
in g406, lines 1630–1641; minimal ray increments, lines 1718–1720. -/
theorem recovers_environment_and_calibrates_ray_of_passage_difference_limits
    (ω : LPPDifferentiability.Environment) (u : Lattice)
    (γ : ℕ → Lattice) (C : Lattice → Lattice → ℝ)
    (_hstart : γ 0 = u)
    (hsteps : IsUpRightRay γ)
    (hsegments : has_maximizing_segments ω γ)
    (hescape₁ : Tendsto (fun n : ℕ => (γ n).1) atTop atTop)
    (hescape₂ : Tendsto (fun n : ℕ => (γ n).2) atTop atTop)
    (hLimit : has_passage_difference_limits ω γ C) :
    recovers_environment ω C ∧
      ∀ n : ℕ, C (γ n) (γ (n + 1)) = ω (γ n) := by
  classical
  -- Source step 1: unit steps make the ray monotone in both coordinates.
  have hmonoγ : Monotone γ := hsteps.monotone

  -- Both coordinate escapes give one entry time beyond both outgoing neighbors.
  have hcommonEntry (x : Lattice) :
      ∃ N : ℕ, x + (1, 0) ≤ γ N ∧ x + (0, 1) ≤ γ N := by
    obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
      ((Filter.tendsto_atTop.1 hescape₁) (x.1 + 1))
    obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.1
      ((Filter.tendsto_atTop.1 hescape₂) (x.2 + 1))
    refine ⟨max n₁ n₂, ?_, ?_⟩
    · constructor
      · change x.1 + 1 ≤ (γ (max n₁ n₂)).1
        exact hn₁ (max n₁ n₂) (le_max_left n₁ n₂)
      · change x.2 + 0 ≤ (γ (max n₁ n₂)).2
        have h := hn₂ (max n₁ n₂) (le_max_right n₁ n₂)
        omega
    · constructor
      · change x.1 + 0 ≤ (γ (max n₁ n₂)).1
        have h := hn₁ (max n₁ n₂) (le_max_left n₁ n₂)
        omega
      · change x.2 + 1 ≤ (γ (max n₁ n₂)).2
        exact hn₂ (max n₁ n₂) (le_max_right n₁ n₂)

  -- Source step 2: the outgoing maximum makes the minimum of the two limits recover ω.
  have hrecovers : ∀ x : Lattice,
      min (C x (x + (1, 0))) (C x (x + (0, 1))) = ω x := by
    intro x
    obtain ⟨N, hEast, hNorth⟩ := hcommonEntry x
    have hxN : x ≤ γ N := by
      constructor
      · have h := hEast.1
        change x.1 + 1 ≤ (γ N).1 at h
        omega
      · have h := hNorth.2
        change x.2 + 1 ≤ (γ N).2 at h
        omega
    have hvalidEast (n : ℕ) : x + (1, 0) ≤ γ (N + n) :=
      le_trans hEast (hmonoγ (Nat.le_add_right N n))
    have hvalidNorth (n : ℕ) : x + (0, 1) ≤ γ (N + n) :=
      le_trans hNorth (hmonoγ (Nat.le_add_right N n))
    let fEast : ℕ → ℝ := fun n =>
      lastPassage ω x (natDisplacement x (γ (N + n))) -
        lastPassage ω (x + (1, 0)) (natDisplacement (x + (1, 0)) (γ (N + n)))
    let fNorth : ℕ → ℝ := fun n =>
      lastPassage ω x (natDisplacement x (γ (N + n))) -
        lastPassage ω (x + (0, 1)) (natDisplacement (x + (0, 1)) (γ (N + n)))
    have hLimitEast : Tendsto fEast atTop (𝓝 (C x (x + (1, 0)))) := by
      simpa only [fEast, natDisplacement] using hLimit x (x + (1, 0)) N hxN hEast
    have hLimitNorth : Tendsto fNorth atTop (𝓝 (C x (x + (0, 1)))) := by
      simpa only [fNorth, natDisplacement] using hLimit x (x + (0, 1)) N hxN hNorth

    -- The integer offsets let the exact outgoing recurrence use its natural-index form.
    let horizontalTail (n : ℕ) : ℕ := ((γ (N + n)).1 - x.1).toNat - 1
    let verticalTail (n : ℕ) : ℕ := ((γ (N + n)).2 - x.2).toNat - 1
    have hhorizontal (n : ℕ) : ((γ (N + n)).1 - x.1).toNat = horizontalTail n + 1 := by
      dsimp only [horizontalTail]
      have hpositive : 1 ≤ (γ (N + n)).1 - x.1 := by
        have h := (hvalidEast n).1
        change x.1 + 1 ≤ (γ (N + n)).1 at h
        omega
      have hcast := Int.toNat_of_nonneg (show 0 ≤ (γ (N + n)).1 - x.1 by omega)
      have hsize : 1 ≤ ((γ (N + n)).1 - x.1).toNat := by omega
      omega
    have hvertical (n : ℕ) : ((γ (N + n)).2 - x.2).toNat = verticalTail n + 1 := by
      dsimp only [verticalTail]
      have hpositive : 1 ≤ (γ (N + n)).2 - x.2 := by
        have h := (hvalidNorth n).2
        change x.2 + 1 ≤ (γ (N + n)).2 at h
        omega
      have hcast := Int.toNat_of_nonneg (show 0 ≤ (γ (N + n)).2 - x.2 by omega)
      have hsize : 1 ≤ ((γ (N + n)).2 - x.2).toNat := by omega
      omega
    have hhorizontalNeighbor (n : ℕ) :
        ((γ (N + n)).1 - (x + (1, 0)).1).toNat = horizontalTail n := by
      have hpositive : 1 ≤ (γ (N + n)).1 - x.1 := by
        have h := (hvalidEast n).1
        change x.1 + 1 ≤ (γ (N + n)).1 at h
        omega
      have hcoordinate :
          (γ (N + n)).1 - (x + (1, 0)).1 = (γ (N + n)).1 - x.1 - 1 := by
        simp only [Prod.fst_add]
        omega
      rw [hcoordinate]
      have hpred := int_toNat_sub_one ((γ (N + n)).1 - x.1) hpositive
      have hoffset := hhorizontal n
      omega
    have hverticalNeighbor (n : ℕ) :
        ((γ (N + n)).2 - (x + (0, 1)).2).toNat = verticalTail n := by
      have hpositive : 1 ≤ (γ (N + n)).2 - x.2 := by
        have h := (hvalidNorth n).2
        change x.2 + 1 ≤ (γ (N + n)).2 at h
        omega
      have hcoordinate :
          (γ (N + n)).2 - (x + (0, 1)).2 = (γ (N + n)).2 - x.2 - 1 := by
        simp only [Prod.snd_add]
        omega
      rw [hcoordinate]
      have hpred := int_toNat_sub_one ((γ (N + n)).2 - x.2) hpositive
      have hoffset := hvertical n
      omega
    have hdispEast (n : ℕ) :
        natDisplacement (x + (1, 0)) (γ (N + n)) = (horizontalTail n, verticalTail n + 1) := by
      apply Prod.ext
      · change ((γ (N + n)).1 - (x + (1, 0)).1).toNat = horizontalTail n
        exact hhorizontalNeighbor n
      · have hshift : (x + (1, 0)).2 = x.2 := by simp
        change ((γ (N + n)).2 - (x + (1, 0)).2).toNat = verticalTail n + 1
        rw [hshift]
        exact hvertical n
    have hdispNorth (n : ℕ) :
        natDisplacement (x + (0, 1)) (γ (N + n)) = (horizontalTail n + 1, verticalTail n) := by
      apply Prod.ext
      · have hshift : (x + (0, 1)).1 = x.1 := by simp
        change ((γ (N + n)).1 - (x + (0, 1)).1).toNat = horizontalTail n + 1
        rw [hshift]
        exact hhorizontal n
      · change ((γ (N + n)).2 - (x + (0, 1)).2).toNat = verticalTail n
        exact hverticalNeighbor n
    have houtgoing (n : ℕ) :
        lastPassage ω x (natDisplacement x (γ (N + n))) =
          ω x + max
            (lastPassage ω (x + (1, 0))
              (natDisplacement (x + (1, 0)) (γ (N + n))))
            (lastPassage ω (x + (0, 1))
              (natDisplacement (x + (0, 1)) (γ (N + n)))) := by
      rw [hdispEast n, hdispNorth n]
      simpa only [natDisplacement, hhorizontal n, hvertical n] using
        lastPassage_outgoing_succ_succ ω x
          (horizontalTail n) (verticalTail n)
    have hminimum (n : ℕ) : min (fEast n) (fNorth n) = ω x := by
      dsimp only [fEast, fNorth]
      let passageAtX : ℝ := lastPassage ω x (natDisplacement x (γ (N + n)))
      let passageEast : ℝ := lastPassage ω (x + (1, 0))
        (natDisplacement (x + (1, 0)) (γ (N + n)))
      let passageNorth : ℝ := lastPassage ω (x + (0, 1))
        (natDisplacement (x + (0, 1)) (γ (N + n)))
      have hmaximum : passageAtX = ω x + max passageEast passageNorth := by
        dsimp only [passageAtX, passageEast, passageNorth]
        exact houtgoing n
      change min (passageAtX - passageEast) (passageAtX - passageNorth) = ω x
      rcases le_total passageEast passageNorth with hEN | hNE
      · rw [max_eq_right hEN] at hmaximum
        have hright : passageAtX - passageNorth = ω x := by linarith
        have horder : passageAtX - passageNorth ≤ passageAtX - passageEast := by linarith
        rw [min_eq_right horder, hright]
      · rw [max_eq_left hNE] at hmaximum
        have hleft : passageAtX - passageEast = ω x := by linarith
        have horder : passageAtX - passageEast ≤ passageAtX - passageNorth := by linarith
        rw [min_eq_left horder, hleft]

    -- The real minimum is continuous, so its limit is the minimum of the two C values.
    have hminimumLimit :
        Tendsto (fun n : ℕ => fEast n ⊓ fNorth n) atTop
          (𝓝 (C x (x + (1, 0)) ⊓ C x (x + (0, 1)))) :=
      hLimitEast.inf_nhds hLimitNorth
    have hconstantSequence :
        (fun n : ℕ => fEast n ⊓ fNorth n) = fun _ : ℕ => ω x := by
      funext n
      exact hminimum n
    rw [hconstantSequence] at hminimumLimit
    have hconstantLimit : Tendsto (fun _ : ℕ => ω x) atTop (𝓝 (ω x)) :=
      tendsto_const_nhds
    have hvalue := tendsto_nhds_unique hminimumLimit hconstantLimit
    change min (C x (x + (1, 0))) (C x (x + (0, 1))) = ω x
    exact hvalue

  -- Source step 3: split the supplied maximizing segment at its actual first ray edge.
  have hpassageDifference (k n : ℕ) :
      lastPassage ω (γ k) (natDisplacement (γ k) (γ ((k + 1) + n))) -
        lastPassage ω (γ (k + 1))
          (natDisplacement (γ (k + 1)) (γ ((k + 1) + n))) = ω (γ k) := by
    have hsegment := hsegments k (n + 1) (by omega)
    obtain ⟨d, p, hdlength, htrace, hmaximizing⟩ := hsegment
    have hendIndex : k + (n + 1) = (k + 1) + n := by omega
    have htraceEnd :
        p.vertex (Fin.last (d.1 + d.2)) = γ (k + (n + 1)) := by
      simpa only [Fin.val_last, hdlength] using htrace (Fin.last (d.1 + d.2))
    have hend : γ k + ((d.1 : ℤ), (d.2 : ℤ)) = γ ((k + 1) + n) := by
      calc
        _ = p.vertex (Fin.last (d.1 + d.2)) := p.finish.symm
        _ = γ (k + (n + 1)) := htraceEnd
        _ = γ ((k + 1) + n) := congrArg γ hendIndex
    have htotal : d = natDisplacement (γ k) (γ ((k + 1) + n)) :=
      natDisplacement_unique (γ k) (γ ((k + 1) + n)) d hend (hmonoγ (by omega))
    let first : Fin (d.1 + d.2 + 1) := ⟨1, by rw [hdlength]; omega⟩
    have hfirstIndex : k + first.val = k + 1 := by simp [first]
    have hfirstVertex : p.vertex first = γ (k + 1) := by
      have h := htrace first
      rw [hfirstIndex] at h
      exact h
    have hsplitVertex :
        γ k + (((p.splitDisplacement first).1 : ℤ),
          ((p.splitDisplacement first).2 : ℤ)) = γ (k + 1) := by
      calc
        _ = p.vertex first := (p.split_vertex first).symm
        _ = γ (k + 1) := hfirstVertex
    have hfirstDirection :
        p.splitDisplacement first = (1, 0) ∨ p.splitDisplacement first = (0, 1) := by
      rcases hsteps k with he | hn
      · left
        have h := hsplitVertex
        rw [he] at h
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        simp only [Prod.fst_add, Prod.snd_add] at h₁ h₂
        apply Prod.ext <;> omega
      · right
        have h := hsplitVertex
        rw [hn] at h
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        simp only [Prod.fst_add, Prod.snd_add] at h₁ h₂
        apply Prod.ext <;> omega
    have hfirstDisplacement :
        p.splitDisplacement first = natDisplacement (γ k) (γ (k + 1)) :=
      natDisplacement_unique (γ k) (γ (k + 1)) (p.splitDisplacement first)
        hsplitVertex (hmonoγ (by omega))
    have hdisplacementAdd := natDisplacement_add (γ k) (γ (k + 1))
      (γ ((k + 1) + n)) (hmonoγ (by omega)) (hmonoγ (by omega))
    have htail : d - p.splitDisplacement first =
        natDisplacement (γ (k + 1)) (γ ((k + 1) + n)) := by
      have htotal₁ := congrArg Prod.fst htotal
      have htotal₂ := congrArg Prod.snd htotal
      have hfirst₁ := congrArg Prod.fst hfirstDisplacement
      have hfirst₂ := congrArg Prod.snd hfirstDisplacement
      have hadd₁ := congrArg Prod.fst hdisplacementAdd
      have hadd₂ := congrArg Prod.snd hdisplacementAdd
      apply Prod.ext
      · simp only [Prod.fst_sub, Prod.fst_add] at htotal₁ hfirst₁ hadd₁ ⊢
        omega
      · simp only [Prod.snd_sub, Prod.snd_add] at htotal₂ hfirst₂ hadd₂ ⊢
        omega
    have hfirstPassage : lastPassage ω (γ k) (p.splitDisplacement first) = ω (γ k) := by
      rcases hfirstDirection with he | hn
      · rw [he]
        exact lastPassage_horizontal_one ω (γ k)
      · rw [hn]
        exact lastPassage_vertical_one ω (γ k)
    have hsplit := p.lastPassage_eq_split_of_maximizing ω hmaximizing first
    rw [hfirstPassage, hsplitVertex, htail, htotal] at hsplit
    -- The split identity now has the literal two passage differences in the target.
    dsimp only [natDisplacement] at hsplit ⊢
    linarith

  -- Source steps 4–5: the edge difference is constant on the common valid tail.
  have hcalibration : ∀ k : ℕ, C (γ k) (γ (k + 1)) = ω (γ k) := by
    intro k
    have hlimit :
        Tendsto (fun n : ℕ =>
          lastPassage ω (γ k)
              (((γ ((k + 1) + n)).1 - (γ k).1).toNat,
                ((γ ((k + 1) + n)).2 - (γ k).2).toNat) -
            lastPassage ω (γ (k + 1))
              (((γ ((k + 1) + n)).1 - (γ (k + 1)).1).toNat,
                ((γ ((k + 1) + n)).2 - (γ (k + 1)).2).toNat))
          atTop (𝓝 (C (γ k) (γ (k + 1)))) := by
      simpa only [natDisplacement] using hLimit (γ k) (γ (k + 1)) (k + 1)
        (hmonoγ (by omega)) le_rfl
    have hconstant :
        (fun n : ℕ =>
          lastPassage ω (γ k)
              (((γ ((k + 1) + n)).1 - (γ k).1).toNat,
                ((γ ((k + 1) + n)).2 - (γ k).2).toNat) -
            lastPassage ω (γ (k + 1))
              (((γ ((k + 1) + n)).1 - (γ (k + 1)).1).toNat,
                ((γ ((k + 1) + n)).2 - (γ (k + 1)).2).toNat)) =
          fun _ : ℕ => ω (γ k) := by
      funext n
      exact hpassageDifference k n
    rw [hconstant] at hlimit
    have hconstantLimit : Tendsto (fun _ : ℕ => ω (γ k)) atTop (𝓝 (ω (γ k))) :=
      tendsto_const_nhds
    exact tendsto_nhds_unique hlimit hconstantLimit

  exact ⟨hrecovers, hcalibration⟩

end LPP.Busemann
