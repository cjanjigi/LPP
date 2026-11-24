/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.SelectedGridPaths.Coarse.Block
import all Differentiability.FinalDraft.SelectedGridPaths.Fine
import Differentiability.Model.Paths.GridCoarseGeneralMerge
import Mathlib.Tactic

/-! The first meeting and the two selected pieces after the crossing, item (U4). -/

public section

namespace LPPDifferentiability.SelectedGridPaths.CoarseBlock
open StairGeometry Set
open scoped Classical

private theorem checked_endpoints {Q : Set Lattice} {b : Lattice → Bool} {y : ℕ → Lattice}
    {n : ℕ} {p : PackedPath} (h : checkedPath Q b y n = some p) :
    p.1 = y 0 ∧ p.1 + ((p.2.1.1 : ℤ), (p.2.1.2 : ℤ)) = y n ∧
      p.2.1.1 + p.2.1.2 = n ∧ ∀ i, p.2.2.vertex i = y i.val := by
  obtain ⟨_, h0, hn, hv, _⟩ := checkedPath_spec h
  exact ⟨h0, by simpa only [p.2.2.finish, Fin.val_last, hn] using hv (Fin.last _), hn, hv⟩

/-- At the literal terminal window of a capped trial, the canonical merge has
a strict interior first meeting. Both pieces at that meeting are in `P_k`. -/
theorem selected_merge
    {a cstar A R C₁ : ℝ} {m : ℕ → ℕ} {k K₁ K₃ : ℕ} {u : Lattice}
    (C : CoarseBlock a cstar A R C₁ m k u) (ω : Environment) (T D B : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃)
    (v : Lattice) (hv : v ∈ C.sites) :
    let b := siteMask ω T
    let Q := workingRegion a A R C₁ m k
    let θ := slopeCutoff a
    let Δ := deviationBound K₁ K₃
    let Λ := C.upperLevel
    let n := (Λ - lev v).toNat
    let ρ := transverse a u
    let g := gammaStream b a u (lev v)
    ω ∈ goodEvent θ K₁ K₃ T Q → gammaDefined Q b a u C.I →
    gammaDefined Q b a u Λ → gammaPoint b a u C.I ∉ forwardTrapped ω T →
    v ∈ Q → v ∉ forwardTrapped ω T →
    Λ - (C.inset : ℤ) - (trimLength θ K₁ K₃ : ℤ) ≤ lev v → lev v < Λ →
    transverse a (g 0) < transverse a v →
    |(ρ - 2 * (Δ : ℝ) - 3) - transverse a v| ≤ 4 * θ * (n : ℝ) →
    |transverse a v - ρ| ≤ D → 2 * (Δ : ℝ) + 3 ≤ D → D + (Δ : ℝ) + 1 ≤ B →
    (∀ y : Lattice, C.I ≤ lev y → lev y ≤ Λ → |transverse a y - ρ| ≤ B → y ∈ Q) →
    ∃ i : ℕ, 0 < i ∧ i < n ∧ firstMeeting Q b a Δ u v Λ = some i ∧
      ∃ p₃ ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b,
      ∃ p₄ ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b,
        p₃.1 = v ∧ p₃.1 + ((p₃.2.1.1 : ℤ), (p₃.2.1.2 : ℤ)) = g i ∧
        p₄.1 = g i ∧ p₄.1 + ((p₄.2.1.1 : ℤ), (p₄.2.1.2 : ℤ)) = gammaPoint b a u Λ ∧
        p₃.2.1.1 + p₃.2.1.2 = i ∧ p₄.2.1.1 + p₄.2.1.2 = n - i ∧
        (∀ j, |transverse a (p₃.2.2.vertex j) - ρ| ≤ B) ∧
        (∀ j, |transverse a (p₄.2.2.vertex j) - ρ| ≤ B) := by
  intro b Q θ Δ Λ n ρ g hE hγ hγend hgt hvQ hnt hwin hvend hstart hslope hvD hD hB hQ
  let X := mergeStream b a Δ u v Λ
  have hθ : 0 < θ := div_pos (lt_min ha₀ (sub_pos.mpr ha₁)) (by norm_num)
  have hθ' : θ ≤ 1 / 10 := by
    unfold θ slopeCutoff
    linarith [min_le_left a (1 - a), min_le_right a (1 - a)]
  have hn : 0 < n := by dsimp [n]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnZ : (n : ℤ) = Λ - lev v := Int.toNat_of_nonneg (by omega)
  have hvI : C.I ≤ lev v := by
    have h : C.I + (C.inset : ℤ) ≤ lev v := hv.1
    omega
  have hΔ : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
  let target := ρ - 2 * (Δ : ℝ) - 3
  let q : ℝ := (target + a * (Λ : ℝ) - v.1) / ((Λ - lev v : ℤ) : ℝ)
  have hline : (q - a) * (n : ℝ) = target - transverse a v := by
    have hΛ : (Λ : ℝ) = (v.1 : ℝ) + v.2 + n := by exact_mod_cast (show Λ = v.1 + v.2 + (n : ℤ) by
      unfold lev at hnZ; omega)
    unfold q
    rw [← hnZ, Int.cast_natCast, sub_mul, div_mul_cancel₀ _ hnR.ne', hΛ]
    unfold transverse
    ring
  have hθa : 5 * θ ≤ a := by unfold θ slopeCutoff; linarith [min_le_left a (1 - a)]
  have hθb : 5 * θ ≤ 1 - a := by unfold θ slopeCutoff; linarith [min_le_right a (1 - a)]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hslope
  have hq₁ : θ ≤ q := le_of_mul_le_mul_right
    (by nlinarith [mul_le_mul_of_nonneg_right hθa hnR.le]) hnR
  have hq₂ : q ≤ 1 - θ := le_of_mul_le_mul_right
    (by nlinarith [mul_le_mul_of_nonneg_right hθb hnR.le]) hnR
  have hX : X = GreedyAttachment.vertex v q (forwardTrapped ω T) := by
    simp only [X, mergeStream, forwardStream, b, forwardTrapped_mask, q, target, ρ]
  have hX0 : X 0 = v := by rw [hX, GreedyAttachment.vertex_zero]
  have hXl (s : ℕ) : lev (X s) = lev v + (s : ℤ) := by
    rw [hX]
    exact GreedyAttachment.level _ _ _ _
  have hXs (s : ℕ) : X (s + 1) = X s + (1, 0) ∨ X (s + 1) = X s + (0, 1) := by
    rw [hX]
    exact GreedyAttachment.step _ _ _ _
  have hTρ : |target - ρ| ≤ D := by unfold target; rw [abs_le]; constructor <;> linarith
  have hband (s : ℕ) (hs : s ≤ n) (E : ℝ)
      (hd : |GreedyAttachment.deviation v q s (X s)| ≤ E) :
      |transverse a (X s) - ρ| ≤ D + E :=
    line_transverse_le a q ρ D E target v (X s) s n hn hs hline hvD hTρ (hXl s) hd
  have hmargin (s : ℕ) (hs : s ≤ n) (hd : |GreedyAttachment.deviation v q s (X s)| ≤ (Δ : ℝ) + 1) :
      X s ∈ Q := hQ _ (by rw [hXl]; omega) (by rw [hXl]; omega)
        ((hband s hs _ hd).trans (by linarith only [hB]))
  have hgeo := greedy_forward_in_region ω T θ K₃ K₁ Q hθ hθ' hK₃ hK₁ hE v hvQ hnt q hq₁ hq₂ n
    (fun s hs hd => by
      change GreedyAttachment.vertex v q (forwardTrapped ω T) s ∈ Q
      change |GreedyAttachment.deviation v q s (GreedyAttachment.vertex v q
        (forwardTrapped ω T) s)| ≤ (Δ : ℝ) + 1 at hd
      rw [← hX] at hd ⊢
      exact hmargin s hs hd)
  have hG (s : ℕ) (hs : s ≤ n) :
      X s ∈ Q ∧ b (X s) = false ∧ |GreedyAttachment.deviation v q s (X s)| ≤ (Δ : ℝ) := by
    have h := hgeo s hs
    rw [hX]
    exact ⟨h.1, (siteMask_eq_false_iff ω T _).mpr h.2.2.1, h.2.2.2⟩
  have hlocX (s : ℕ) (hs : s ≤ n) :
      |transverse a (X s) - ρ| ≤ B := (hband s hs _ (hG s hs).2.2).trans (by linarith only [hB])
  have hgdef (s : ℕ) (hs : s ≤ n) : gammaDefined Q b a u (lev v + (s : ℤ)) :=
    gammaDefined_between hγ hγend (by omega) (by omega)
  have hg (s : ℕ) (hs : s ≤ n) :
      g s ∈ Q ∧ b (g s) = false ∧ |transverse a (g s) - ρ| ≤ (Δ : ℝ) :=
    gammaPoint_bounds b a K₁ K₃ Q ha₀ ha₁ hK₁ hK₃ (goodEvent_siteMask hE) u C.site_mem _ (hgdef s hs)
  have hgl (s : ℕ) : lev (g s) = lev v + (s : ℤ) := gammaPoint_level _ _ _ _
  have hgs (s : ℕ) : g (s + 1) = g s + (1, 0) ∨ g (s + 1) = g s + (0, 1) := by
    simpa only [g, gammaStream, Nat.cast_add, Nat.cast_one, add_assoc] using
      gammaPoint_step b a u (lev v + (s : ℤ))
  have hlast : transverse a (X n) < transverse a (g n) := by
    have H := transverse_line_difference a q v (X n) (n : ℤ) (hXl n)
    simp only [Int.cast_natCast] at H
    rw [mul_comm (n : ℝ), hline, add_sub_cancel] at H
    change transverse a (X n) - target = GreedyAttachment.deviation v q n (X n) at H
    have h₁ := (abs_le.mp (hG n le_rfl).2.2).2
    have h₂ := (abs_le.mp (hg n le_rfl).2.2).1
    unfold target at H
    linarith only [H, h₁, h₂]
  obtain ⟨eX, pX, heX, hnX, hvX, _⟩ := exists_path_of_seq X n (fun s _ => hXs s)
  obtain ⟨eg, pg, heg, hng, hvg, _⟩ := exists_path_of_seq g n (fun s _ => hgs s)
  obtain ⟨i₀, hi₀, _, hmeet⟩ := paths_merge a (X 0) (g 0) eX eg pX pg
    (by change lev (X 0) = lev (g 0); rw [hXl, hgl])
    (hnX.trans hng.symm) (by rwa [hX0]) (by rw [heX, heg]; exact hlast)
  have hmeet' : X i₀ = g i₀ := by
    simpa only [hvX, hvg] using hmeet
  let P (i : ℕ) := i ≤ n ∧ gammaDefined Q b a u (lev v + (i : ℤ)) ∧ X i = g i
  have hex : ∃ i, P i := ⟨i₀, by omega, hgdef i₀ (by omega), hmeet'⟩
  let i := Nat.find hex
  have hi : P i := Nat.find_spec hex
  have hin : i < n := lt_of_le_of_lt (Nat.find_min' hex (show P i₀ from
    ⟨by omega, hgdef i₀ (by omega), hmeet'⟩)) (by omega)
  have hip : 0 < i := by
    by_contra! h
    have he : i = 0 := by omega
    have H := hi.2.2
    rw [he, hX0] at H
    exact hstart.ne (congrArg (transverse a) H).symm
  have hmeetFirst : firstMeeting Q b a Δ u v Λ = some i := by
    unfold firstMeeting
    exact dite_eq_left hex
  let Y := gammaStream b a u (lev v + (i : ℤ))
  have hY (s : ℕ) : Y s = g (i + s) := by simp only [Y, g, gammaStream, Nat.cast_add, add_assoc]
  have h₃ : admissibleIn Q b X i :=
    ⟨fun s _ => hXs s, fun s hs => (hG s (by omega)).1, fun s hs => (hG s (by omega)).2.1⟩
  have h₄ : admissibleIn Q b Y (n - i) := by
    refine ⟨fun s _ => ?_, fun s hs => ?_, fun s hs => ?_⟩
    · rw [hY, hY, ← Nat.add_assoc]
      exact hgs (i + s)
    · rw [hY]
      exact (hg _ (by omega)).1
    · rw [hY]
      exact (hg _ (by omega)).2.1
  obtain ⟨p₃, hp₃⟩ := checkedPath_exists h₃
  obtain ⟨p₄, hp₄⟩ := checkedPath_exists h₄
  have hset : mergeChoices Q b a Δ u v C.I Λ =
      insert p₃ (Option.toFinset (some p₄)) := by
    unfold mergeChoices
    rw [ite_eq_left ⟨hγ, by simpa only [b, forwardTrapped_mask] using hgt,
      by simpa only [b, forwardTrapped_mask] using hnt⟩, hmeetFirst]
    change (match checkedPath Q b X i with
      | none => ∅
      | some p => insert p (if gammaDefined Q b a u Λ then (checkedPath Q b Y (n - i)).toFinset else ∅)) = _
    rw [hp₃]
    simp only [hγend, ite_true, hp₄]
  have hm₃ : p₃ ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b :=
    C.merge_mem hv hwin (by rw [hset]; exact Finset.mem_insert_self _ _)
  have hm₄ : p₄ ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b :=
    C.merge_mem hv hwin (by rw [hset]; exact Finset.mem_insert_of_mem (by simp))
  obtain ⟨h30, h3end, h3len, h3v⟩ := checked_endpoints hp₃
  obtain ⟨h40, h4end, h4len, h4v⟩ := checked_endpoints hp₄
  have hYend : Y (n - i) = gammaPoint b a u Λ := by
    rw [hY, Nat.add_sub_cancel' hin.le]
    change gammaPoint b a u (lev v + (n : ℤ)) = gammaPoint b a u Λ
    rw [show lev v + (n : ℤ) = Λ by omega]
  refine ⟨i, hip, hin, hmeetFirst, p₃, hm₃, p₄, hm₄, h30.trans hX0,
    h3end.trans hi.2.2, h40.trans (by rw [hY, Nat.add_zero]), h4end.trans hYend, h3len, h4len, ?_, ?_⟩
  · intro j
    rw [h3v]
    exact hlocX _ (by have := j.isLt; omega)
  · intro j
    rw [h4v, hY]
    apply (hg _ (by have := j.isLt; omega)).2.2.trans
    linarith only [hD, hB, hΔ]

end LPPDifferentiability.SelectedGridPaths.CoarseBlock
