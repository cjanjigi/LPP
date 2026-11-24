/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.SelectedGridPaths.Coarse.Block
import all Differentiability.FinalDraft.SelectedGridPaths.Fine
import Differentiability.FinalDraft.StairGeometry.Arrival
import LPP_Foundations.Model.Paths.Level
import Mathlib.Tactic

/-! The actual selected arrival to the trimmed crossing start, item (U4). -/

public section

namespace LPPDifferentiability.SelectedGridPaths.CoarseBlock
open StairGeometry Set
open scoped Classical

private theorem boxFree_mask {ω : Environment} {T : ℝ} {L : ℕ} {v : Lattice}
    (h : boxFree ω T L v) : boxFree (maskEnvironment (siteMask ω T)) 0 L v := by
  intro y hy₁ hy₂ hy₃ hy₄
  rw [neg_zero, maskEnvironment_nonneg_iff, siteMask_eq_false_iff]
  exact h y hy₁ hy₂ hy₃ hy₄

/-- A fixed block's trimmed start is reached by the literal selected
arrival. Its vertices follow the prescribed greedy prefix and the
horizontal-first tail, so no other arrival can be charged to the event. -/
theorem selected_arrival
    {a cstar A R C₁ : ℝ} {m : ℕ → ℕ} {k K₁ K₃ : ℕ} {u : Lattice}
    (C : CoarseBlock a cstar A R C₁ m k u) (ω : Environment) (T D B : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃)
    (v : Lattice) (hv : v ∈ C.sites) :
    let b := siteMask ω T
    let Q := workingRegion a A R C₁ m k
    let θ := slopeCutoff a
    let L := arrivalBoxSize θ K₁ K₃
    let Δ := deviationBound K₁ K₃
    let z := gammaPoint b a u C.I
    let n := (lev v - C.I).toNat
    ω ∈ goodEvent θ K₁ K₃ T Q → gammaDefined Q b a u C.I → z ∉ forwardTrapped ω T →
    lev v ≤ C.I + (C.inset : ℤ) + (trimLength θ K₁ K₃ : ℤ) →
    boxFree ω T L v → L ≤ n →
    |transverse a v - transverse a z| ≤ 4 * θ * (n : ℝ) →
    |transverse a z - transverse a u| ≤ D → |transverse a v - transverse a u| ≤ D →
    D + (Δ : ℝ) + (L : ℝ) ≤ B →
    (∀ y : Lattice, C.I ≤ lev y → lev y ≤ C.upperLevel →
      |transverse a y - transverse a u| ≤ B → y ∈ Q) →
    ∃ q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b,
      q.1 = z ∧ q.1 + ((q.2.1.1 : ℤ), (q.2.1.2 : ℤ)) = v ∧
      q.2.1.1 + q.2.1.2 = n ∧
      (∀ i, |transverse a (q.2.2.vertex i) - transverse a u| ≤ B) := by
  intro b Q θ L Δ z n hE hγ hnt htrim hbox hL hs hzD hvD hB hQ
  have hzQ : z ∈ Q :=
    (gammaPoint_bounds b a K₁ K₃ Q ha₀ ha₁ hK₁ hK₃ (goodEvent_siteMask hE) u C.site_mem C.I hγ).1
  have hzlev : lev z = C.I := gammaPoint_level _ _ _ _
  have hvlo : C.I + (C.inset : ℤ) ≤ lev v := hv.1
  have hvhi : lev v ≤ C.upperLevel := by
    have h : lev v ≤ C.I + (C.ell : ℤ) - (C.inset : ℤ) := hv.2.1
    change lev v ≤ C.I + (C.ell : ℤ)
    omega
  have hlev : v.1 + v.2 = z.1 + z.2 + (n : ℤ) := by
    have hn : (n : ℤ) = lev v - C.I := Int.toNat_of_nonneg (by omega)
    change lev v = lev z + (n : ℤ)
    omega
  have hlen : (v.1 - z.1 + (v.2 - z.2)).toNat = n := by
    change (v.1 - z.1 + (v.2 - z.2)).toNat = (lev v - C.I).toNat
    change z.1 + z.2 = C.I at hzlev
    unfold lev
    omega
  have hθ : 0 < θ := div_pos (lt_min ha₀ (sub_pos.mpr ha₁)) (by norm_num)
  have hL0 : 0 < L := Nat.ceil_pos.mpr (by positivity)
  have hn : 0 < n := hL0.trans_le hL
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let q : ℝ := ((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ)
  have hqn : q * (n : ℝ) = ((v.1 - z.1 : ℤ) : ℝ) := div_mul_cancel₀ _ hnR.ne'
  have hline : (q - a) * (n : ℝ) = transverse a v - transverse a z := by
    have H := transverse_line_difference a a z v (n : ℤ) hlev
    simp only [sub_self, mul_zero, add_zero, Int.cast_natCast] at H
    rw [H, sub_mul, hqn, Int.cast_sub]
    ring
  obtain ⟨hlo, hhi⟩ := abs_le.mp hs
  have hθa : 5 * θ ≤ a := by unfold θ slopeCutoff; linarith [min_le_left a (1 - a)]
  have hθb : 5 * θ ≤ 1 - a := by unfold θ slopeCutoff; linarith [min_le_right a (1 - a)]
  have hq₁ : θ ≤ q := le_of_mul_le_mul_right
    (by nlinarith [mul_le_mul_of_nonneg_right hθa hnR.le]) hnR
  have hq₂ : q ≤ 1 - θ := le_of_mul_le_mul_right
    (by nlinarith [mul_le_mul_of_nonneg_right hθb hnR.le]) hnR
  have h₁ : z.1 ≤ v.1 := by
    have h : (0 : ℝ) ≤ ((v.1 - z.1 : ℤ) : ℝ) :=
      hqn ▸ mul_nonneg (hθ.le.trans hq₁) hnR.le
    exact sub_nonneg.mp (by exact_mod_cast h)
  have h₂ : z.2 ≤ v.2 := by
    have H : (v.1 : ℝ) + v.2 = z.1 + z.2 + n := by exact_mod_cast hlev
    have h := mul_le_mul_of_nonneg_right (hq₂.trans (sub_le_self _ hθ.le)) hnR.le
    rw [hqn, Int.cast_sub, one_mul] at h
    exact_mod_cast (show (z.2 : ℝ) ≤ v.2 by linarith only [H, h])
  have hloc (y : Lattice) (s : ℕ) (hsn : s ≤ n) (hsy : lev y = lev z + (s : ℤ))
      (E : ℝ) (hdev : |GreedyAttachment.deviation z q s y| ≤ E) :
      |transverse a y - transverse a u| ≤ D + E :=
    line_transverse_le a q (transverse a u) D E (transverse a v) z y s n hn hsn hline hzD hvD hsy hdev
  have hmargin (y : Lattice) (hlo : lev z ≤ lev y) (hhi : lev y ≤ lev v)
      (hd : |GreedyAttachment.deviation z q (lev y - lev z).toNat y| ≤ (Δ : ℝ)) :
      y ∈ Q := by
    let s := (lev y - lev z).toNat
    have hsy : lev y = lev z + (s : ℤ) := by dsimp [s]; omega
    have hsn : s ≤ n := by change lev v = lev z + (n : ℤ) at hlev; omega
    exact hQ y (hzlev ▸ hlo) (hhi.trans hvhi)
      ((hloc y s hsn hsy Δ hd).trans (by linarith [Nat.cast_nonneg (α := ℝ) L]))
  have hp := arrival_path ω T a K₁ K₃ Q ha₀ ha₁ hK₁ hK₃ hE z v hzQ hnt h₁ h₂
  have ha := arrival_pieces ω T a K₁ K₃ Q ha₀ ha₁ hK₁ hK₃ hE z v hzQ hnt h₁ h₂
  dsimp only at hp ha
  rw [hlen] at hp ha
  obtain ⟨d, p, hf, hd, hprefix, htail, hgood, hdev⟩ := hp hL hq₁ hq₂ hbox hmargin
  obtain ⟨_, _, hetail, _, _, _, _⟩ := ha hL hq₁ hq₂ hbox hmargin
  let x := forwardGreedy ω T z hnt q
  let e : ℕ × ℕ := ((v.1 - (x (n - L)).1).toNat, (v.2 - (x (n - L)).2).toNat)
  have he : e.1 + e.2 = L := hetail
  have hx : forwardStream b (((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ)) z = x := by
    simp only [forwardStream, b, forwardTrapped_mask, x, forwardGreedy, q]
  let y := arrivalStream b L z v
  have hstream (i : Fin (d.1 + d.2 + 1)) : p.vertex i = y i.val := by
    have hi := i.isLt
    have hn' : (lev v - lev z).toNat = n := by rw [hzlev]
    unfold y arrivalStream
    rw [hn']
    dsimp only
    rw [hx]
    by_cases h : i.val ≤ n - L
    · rw [ite_eq_left h]
      exact hprefix i h
    · rw [ite_eq_right h]
      let j : Fin (e.1 + e.2 + 1) := ⟨i.val - (n - L), by omega⟩
      have hj : i.val = n - L + j.val := by dsimp only [j]; omega
      exact (htail j i hj).1
  have hpB (i : Fin (d.1 + d.2 + 1)) : |transverse a (p.vertex i) - transverse a u| ≤ B :=
    (hloc _ i.val (by have := i.isLt; omega) (p.level i) _ (hdev i)).trans (by linarith only [hB])
  have hpQ (i : Fin (d.1 + d.2 + 1)) : p.vertex i ∈ Q := by
    have hi := i.isLt
    have hl := p.level i
    change lev (p.vertex i) = lev z + (i.val : ℤ) at hl
    change lev v = lev z + (n : ℤ) at hlev
    exact hQ _ (by omega) (by omega) (hpB i)
  have hy : admissibleIn Q b y n := ⟨fun i hi => by
      have H := p.step ⟨i, by omega⟩
      simpa only [hstream, Fin.val_succ, Fin.val_castSucc] using H,
    fun i hi => by
      let j : Fin (d.1 + d.2 + 1) := ⟨i, by omega⟩
      rw [← (show p.vertex j = y i from hstream j)]
      exact hpQ j,
    fun i hi => by
      let j : Fin (d.1 + d.2 + 1) := ⟨i, by omega⟩
      rw [← (show p.vertex j = y i from hstream j)]
      exact (siteMask_eq_false_iff ω T _).mpr (hgood j (by dsimp [j]; omega))⟩
  obtain ⟨s, hs⟩ := checkedPath_exists hy
  have hyv : y n = v := by
    simpa only [Fin.val_last, hd, p.finish, hf] using (hstream (Fin.last (d.1 + d.2))).symm
  have hchoice : arrivalChoice Q b a L u v C.I = some s := by
    unfold arrivalChoice
    rw [ite_eq_left ⟨hγ, by simpa only [b, forwardTrapped_mask] using hnt, boxFree_mask hbox, hL, hyv⟩]
    exact hs
  obtain ⟨_, hs0, hslen, hsv, _⟩ := checkedPath_spec hs
  have hy0 : y 0 = z := by simpa only [p.start, Fin.val_zero] using (hstream 0).symm
  refine ⟨s, C.arrival_mem hv htrim hchoice, hs0.trans hy0, ?_, hslen, fun i => ?_⟩
  · simpa only [Fin.val_last, hslen, hyv, s.2.2.finish] using hsv (Fin.last (s.2.1.1 + s.2.1.2))
  · rw [hsv]
    have hi := i.isLt
    let j : Fin (d.1 + d.2 + 1) := ⟨i.val, by omega⟩
    rw [← (show p.vertex j = y i.val from hstream j)]
    exact hpB j

end LPPDifferentiability.SelectedGridPaths.CoarseBlock
