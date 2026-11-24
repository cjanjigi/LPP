/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.SelectedGridPaths.Membership
public import Differentiability.Model.Paths.GridConnectionsGeneral
import all Differentiability.Model.Paths.GridFineGeneral
import Mathlib.Tactic

/-! The fine grid path and its cost in (U1) and (U6) of Appendix B. -/

public section

namespace LPPDifferentiability.SelectedGridPaths
open StairGeometry Set
open scoped Classical

private theorem goodEvent_siteMask {ω : Environment} {T a : ℝ} {K₁ K₃ : ℕ} {Q : Set Lattice}
    (h : ω ∈ goodEvent (slopeCutoff a) K₁ K₃ T Q) :
    maskEnvironment (siteMask ω T) ∈ goodEvent (slopeCutoff a) K₁ K₃ 0 Q := by
  have hm (z : Lattice) : maskEnvironment (siteMask ω T) z < 0 ↔ ω z < -T := by
    rw [← not_le, maskEnvironment_nonneg_iff, siteMask_eq_false_iff, not_le]
  simpa only [goodEvent, Set.mem_ofPred_eq, neg_zero, hm, reachSet_mask, reachBackSet_mask] using h

private theorem gammaDefined_between {Q : Set Lattice} {b : Lattice → Bool} {a : ℝ}
    {u : Lattice} {I L J : ℤ} (hI : gammaDefined Q b a u I) (hJ : gammaDefined Q b a u J)
    (hi : I ≤ L) (hj : L ≤ J) : gammaDefined Q b a u L := by
  by_cases e : L = I ∨ L = J
  · rcases e with rfl | rfl <;> assumption
  by_cases hu : lev u ≤ L
  · rcases hJ with ⟨_, ht, hp⟩ | ⟨h, _, _⟩
    · exact Or.inl ⟨hu, ht, fun s hs => hp s (by omega)⟩
    · exact (e (Or.inr (by omega))).elim
  · rcases hI with ⟨h, _, _⟩ | ⟨_, ht, hp⟩
    · exact False.elim (hu (h.trans hi))
    · exact Or.inr ⟨by omega, ht, fun s hs => hp s (by omega)⟩

private theorem gammaPoint_bounds (b : Lattice → Bool) (a : ℝ) (K₁ K₃ : ℕ) (Q : Set Lattice)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃)
    (hE : maskEnvironment b ∈ goodEvent (slopeCutoff a) K₁ K₃ 0 Q)
    (u : Lattice) (hu : u ∈ Q) (I : ℤ) (hdef : gammaDefined Q b a u I) :
    gammaPoint b a u I ∈ Q ∧ b (gammaPoint b a u I) = false ∧
      |transverse a (gammaPoint b a u I) - transverse a u| ≤ (deviationBound K₁ K₃ : ℝ) := by
  have haL : slopeCutoff a ≤ a := by
    unfold slopeCutoff
    linarith [min_le_left a (1 - a)]
  have haR : a ≤ 1 - slopeCutoff a := by
    unfold slopeCutoff
    linarith [min_le_right a (1 - a)]
  rcases hdef with ⟨hI, hnt, hp⟩ | ⟨hI, hnt, hp⟩
  · rw [gammaPoint_eq_forward b a u I hI]
    let n := (I - lev u).toNat
    let p := forwardStream b a u n
    have h := forward_greedy_bound (maskEnvironment b) 0 a K₁ K₃ Q ha₀ ha₁ hK₁ hK₃ hE
      u hu hnt a haL haR n hp n le_rfl
    have hgood : 0 ≤ maskEnvironment b p := by
      simpa only [neg_zero, p, forwardStream, forwardGreedy] using h.2.1
    refine ⟨hp n le_rfl, (maskEnvironment_nonneg_iff b p).mp hgood, ?_⟩
    have hr := transverse_line_difference a a u p (n : ℤ) (GreedyAttachment.level _ _ _ _)
    simp only [sub_self, mul_zero, add_zero, Int.cast_natCast] at hr
    change |transverse a p - transverse a u| ≤ _
    rw [hr]
    exact h.2.2
  · rw [gammaPoint_eq_backward b a u I hI]
    let n := (lev u - I).toNat
    let p := backwardStream b a u n
    have h := backward_greedy_bound (maskEnvironment b) 0 a K₁ K₃ Q ha₀ ha₁ hK₁ hK₃ hE
      u hu hnt a haL haR n hp n le_rfl
    have hgood : 0 ≤ maskEnvironment b p := by
      have hb : -(0 : ℝ) ≤ maskEnvironment b (backwardGreedy (maskEnvironment b) 0 u hnt a n) :=
        not_lt.mp fun hc => h.1 (Or.inl hc)
      simpa only [neg_zero, p, backwardStream, backwardGreedy] using hb
    refine ⟨hp n le_rfl, (maskEnvironment_nonneg_iff b p).mp hgood, ?_⟩
    have hl := GreedyAttachment.level (-u) a {z | -z ∈ backwardBlocked (maskEnvironment b) 0} n
    have hl' : p.1 + p.2 = u.1 + u.2 + (-(n : ℤ)) := by
      simp only [Prod.fst_neg, Prod.snd_neg] at hl
      change -(GreedyAttachment.vertex (-u) a _ n).1 - (GreedyAttachment.vertex (-u) a _ n).2 = _
      omega
    have hr := transverse_line_difference a a u p (-(n : ℤ)) hl'
    simp only [sub_self, mul_zero, add_zero, Int.cast_neg, Int.cast_natCast] at hr
    change |transverse a p - transverse a u| ≤ _
    rw [hr]
    have hn : (p.1 : ℝ) - u.1 - (-(n : ℝ)) * a =
        -GreedyAttachment.deviation (-u) a n (-p) := by
      simp only [GreedyAttachment.deviation, Prod.fst_neg, Int.cast_neg]
      ring
    rw [hn, abs_neg]
    exact h.2

/-- The fine grid connection between two defined staircase vertices. Only
the literal selected fine segment is charged to the weight event. -/
theorem fine_gridConnection (ω : Environment) (T t a G0 dl dr K Cm cstar C₁ A R : ℝ)
    (m : ℕ → ℕ) (k K₁ K₃ j : ℕ) (u : Lattice) (I : ℤ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hdl : |dl| ≤ K) (hdr : |dr| ≤ K) (hG : 0 ≤ G0 + 2 * Cm)
    (hC : 8 * cstar * (G0 + 2 * Cm) + 1 ≤ C₁) (hC1 : 1 ≤ C₁)
    (hwidth : 2 * (deviationBound K₁ K₃ : ℝ) * K ≤ (j : ℝ) ^ 2 * (width k j : ℝ))
    (hu : u ∈ workingRegion a A R C₁ m k) (hj : j ∈ scales (m k))
    (hI : I ∈ gridLevels A (m k) j)
    (hfine : (mesh (m k) j : ℝ) < 8 * (cstar * ((j : ℝ) ^ 2 * (width k j : ℝ))))
    (hE : ω ∈ goodEvent (slopeCutoff a) K₁ K₃ T (workingRegion a A R C₁ m k))
    (hweight : ∀ q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ (siteMask ω T),
      -2 * Cm * ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) - t / 2 ≤ pathWeight ω q.2.2) :
    let b := siteMask ω T
    let Q := workingRegion a A R C₁ m k
    let l := mesh (m k) j
    let P := (j : ℝ) ^ 2 * (width k j : ℝ)
    gammaDefined Q b a u I → gammaDefined Q b a u (I + (l : ℤ)) →
    GridConnection ω a G0 dl dr (C₁ * P + 2 * t) (C₁ * P) u
      (gammaPoint b a u I) (gammaPoint b a u (I + (l : ℤ))) := by
  intro b Q l P hleft hright
  let y := gammaStream b a u I
  have hsite (s : ℕ) (hs : s ≤ l) :
      y s ∈ Q ∧ b (y s) = false ∧ |transverse a (y s) - transverse a u| ≤ (deviationBound K₁ K₃ : ℝ) :=
    gammaPoint_bounds b a K₁ K₃ Q ha₀ ha₁ hK₁ hK₃ (goodEvent_siteMask hE) u hu _
      (gammaDefined_between hleft hright (by omega) (by omega))
  have hx : admissibleIn Q b y l := ⟨fun s _ => by
      simpa only [y, gammaStream, Nat.cast_add, Nat.cast_one, add_assoc] using
        gammaPoint_step b a u (I + (s : ℤ)),
    fun s hs => (hsite s hs).1, fun s hs => (hsite s hs.le).2.1⟩
  obtain ⟨q, hq⟩ := checkedPath_exists hx
  have hq' : fineChoice Q b a u I l = some q := by
    rw [fineChoice, ite_eq_left ⟨hleft, hright⟩]
    exact hq
  have hw := hweight q (fineChoice_mem hu hj hI hfine hq')
  obtain ⟨_, hstart, hl, hv, _⟩ := checkedPath_spec hq
  have hloc (i : Fin (q.2.1.1 + q.2.1.2 + 1)) :
      |transverse a (q.2.2.vertex i) - transverse a u| ≤ (deviationBound K₁ K₃ : ℝ) := by
    rw [hv i]
    exact (hsite _ (by have := i.isLt; omega)).2.2
  have hend := (q.2.2.finish).symm.trans (hv (Fin.last (q.2.1.1 + q.2.1.2)))
  have hstart' : q.1 = gammaPoint b a u I := by simpa only [y, gammaStream, Nat.cast_zero, add_zero] using hstart
  have hh : (l : ℝ) < 8 * cstar * P := by simpa only [P, l, mul_assoc] using hfine
  have hcost := fine_piece ω a G0 dl dr K Cm cstar C₁ t P (deviationBound K₁ K₃ : ℝ)
    (transverse a u) l q.1 q.2.1 q.2.2 hl hloc (by rwa [hl] at hw)
    ht hK hdl hdr hG hC hC1 (Nat.cast_nonneg _) hwidth hh
  rw [← hstart']
  refine ⟨q.2.1, q.2.2, ?_, hcost⟩
  simpa only [Fin.val_last, hl, y, gammaStream] using hend

end LPPDifferentiability.SelectedGridPaths
