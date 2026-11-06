/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.LevelNetCoverage
public import Differentiability.Model.Paths.BackwardReachableLevel
import Mathlib.Tactic

/-! # Attachments from a backward level net -/

public section

namespace LPPDifferentiability

/-- A single level net supplies an actual length-`m` path from one of its net
points to every signed terminal point in the original closed interval. -/
theorem exists_backward_net_attachments
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ)
    (hm : 1 ≤ min a (1 - a) * (m : ℝ) / 4)
    (I : ℤ) (lo hi : ℝ) (hlohi : lo ≤ hi) :
    ∃ (M : ℕ) (v : Fin (M + 1) → Lattice),
      1 ≤ M ∧ Function.Injective v ∧
      (∀ j, (v j).1 + (v j).2 = I - (m : ℤ) ∧
        ((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) ∈
          Set.Icc (lo - (1 - a) * (m : ℝ)) (hi + a * (m : ℝ))) ∧
      (M + 1 : ℝ) <
        4 * (hi - lo + (m : ℝ)) / (min a (1 - a) * (m : ℝ)) ∧
      (∀ w : Lattice, w.1 + w.2 = I →
        ((1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ)) ∈ Set.Icc lo hi →
        ∃ (j : Fin (M + 1)) (d : ℕ × ℕ) (p : Path (v j) d),
          d.1 + d.2 = m ∧
          p.vertex (Fin.last (d.1 + d.2)) = w ∧
          |(1 - a) * (((w - v j).1 : ℤ) : ℝ) -
            a * (((w - v j).2 : ℤ) : ℝ)| ≤ (m : ℝ)) := by
  let A : ℝ := lo - (1 - a) * (m : ℝ)
  let B : ℝ := hi + a * (m : ℝ)
  have hBA : B - A = hi - lo + (m : ℝ) := by
    dsimp [A, B]
    ring
  have hwidth : (m : ℝ) ≤ B - A := by
    rw [hBA]
    have hgap : 0 ≤ hi - lo := sub_nonneg.mpr hlohi
    linarith
  obtain ⟨M, v, hM, hinj, hnet, _hgap, _hfirst, _hlast,
      _hstart, _hend, hcard, hcoverage⟩ :=
    exists_level_net a ha ha1 m hm (I - (m : ℤ)) A B hwidth
  refine ⟨M, v, hM, hinj, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨hlevel, hleft, hright⟩ := hnet j
    refine ⟨hlevel, ?_⟩
    simpa only [Set.mem_Icc, A, B] using And.intro hleft hright
  · rw [hBA] at hcard
    exact hcard
  · intro w hw hinterval
    let rhoW : ℝ := (1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ)
    let gamma : ℝ := rhoW - (1 - a) * (m : ℝ)
    have hleft : A ≤ gamma := by
      dsimp [A, gamma, rhoW]
      linarith [hinterval.1]
    have hright : gamma + (m : ℝ) ≤ B := by
      dsimp [B, gamma, rhoW]
      linarith [hinterval.2]
    obtain ⟨j, hjlo, hjhi⟩ := hcoverage gamma hleft hright
    have hlevel : (v j).1 + (v j).2 + (m : ℤ) = w.1 + w.2 := by
      calc
        (v j).1 + (v j).2 + (m : ℤ) =
            (I - (m : ℤ)) + (m : ℤ) := by rw [(hnet j).1]
        _ = I := by omega
        _ = w.1 + w.2 := hw.symm
    have htransverse :
        ((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) ∈
          Set.Icc
            ((1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ) - (1 - a) * (m : ℝ))
            ((1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ) + a * (m : ℝ)) := by
      constructor
      · have h := hjlo
        dsimp [gamma, rhoW] at h ⊢
        linarith
      · have h := hjhi
        dsimp [gamma, rhoW] at h ⊢
        linarith
    have hreachable :=
      (backwardLevelInterval_iff w (v j) m a).2 ⟨hlevel, htransverse⟩
    have hmem := (backwardReachable_mem_iff w (v j) m).2 hreachable
    obtain ⟨k, p, hfinish⟩ :=
      exists_path_from_backwardReachable w (v j) m hmem
    let d : ℕ × ℕ := (k.val, m - k.val)
    have hlength : d.1 + d.2 = m := by
      dsimp [d]
      omega
    have hfinish' : p.vertex (Fin.last (d.1 + d.2)) = w := by
      simpa [d] using hfinish
    have hsub :
        (1 - a) * (((w - v j).1 : ℤ) : ℝ) -
            a * (((w - v j).2 : ℤ) : ℝ) =
          ((1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ)) -
            ((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) := by
      simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
      ring
    have ham : a * (m : ℝ) ≤ (m : ℝ) := by
      have h := mul_le_mul_of_nonneg_right (le_of_lt ha1) (Nat.cast_nonneg m)
      simpa only [one_mul] using h
    have h1a : 1 - a ≤ 1 := by linarith [ha]
    have h1am : (1 - a) * (m : ℝ) ≤ (m : ℝ) := by
      have h := mul_le_mul_of_nonneg_right h1a (Nat.cast_nonneg m)
      simpa only [one_mul] using h
    rcases htransverse with ⟨htranslo, htranshi⟩
    have hbound :
        -(m : ℝ) ≤ ((1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ)) -
            ((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) ∧
        ((1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ)) -
            ((1 - a) * ((v j).1 : ℝ) - a * ((v j).2 : ℝ)) ≤ (m : ℝ) := by
      constructor
      · have hnegle : -(m : ℝ) ≤ -(a * (m : ℝ)) := neg_le_neg ham
        linarith [htranshi, hnegle]
      ·
        linarith [htranslo, h1am]
    refine ⟨j, d, p, hlength, hfinish', ?_⟩
    rw [hsub]
    exact abs_le.mpr hbound


end LPPDifferentiability
