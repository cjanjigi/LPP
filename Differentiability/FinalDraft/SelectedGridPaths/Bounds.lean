/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.SelectedGridPaths.Family
public import LPP_Foundations.Model.Animals.PathSets
public import Mathlib.Order.Filter.AtTopBot.Basic
import all Differentiability.Probability.StairGeometryEvent
import Differentiability.Analysis.GridScaleCounts
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! The cardinality, length, region, and mask bounds for the paths in Appendix B, item (U5). -/

public section

namespace LPPDifferentiability.SelectedGridPaths

open Filter StairGeometry
open scoped Classical Topology

private theorem fineChoice_checked {Q : Set Lattice} {b : Lattice → Bool} {a : ℝ}
    {u : Lattice} {I : ℤ} {l : ℕ} {q : PackedPath}
    (hq : fineChoice Q b a u I l = some q) :
    checkedPath Q b (gammaStream b a u I) l = some q := by
  unfold fineChoice at hq
  split at hq
  · exact hq
  · cases hq

private theorem arrivalChoice_checked {Q : Set Lattice} {b : Lattice → Bool} {a : ℝ}
    {L : ℕ} {u v : Lattice} {I : ℤ} {q : PackedPath}
    (hq : arrivalChoice Q b a L u v I = some q) :
    checkedPath Q b (arrivalStream b L (gammaPoint b a u I) v) (lev v - I).toNat = some q := by
  unfold arrivalChoice at hq
  dsimp only at hq
  split at hq
  · exact hq
  · cases hq

private theorem firstMeeting_le {Q : Set Lattice} {b : Lattice → Bool} {a : ℝ}
    {Δ₀ i : ℕ} {u v : Lattice} {Λ : ℤ}
    (hi : firstMeeting Q b a Δ₀ u v Λ = some i) : i ≤ (Λ - lev v).toNat := by
  unfold firstMeeting at hi
  dsimp only at hi
  split at hi
  · rename_i h
    rw [← Option.some.inj hi]
    exact (Nat.find_spec h).1
  · cases hi

private theorem mergeChoices_checked {Q : Set Lattice} {b : Lattice → Bool} {a : ℝ}
    {Δ₀ : ℕ} {u v : Lattice} {I Λ : ℤ} {q : PackedPath}
    (hq : q ∈ mergeChoices Q b a Δ₀ u v I Λ) :
    ∃ y n, checkedPath Q b y n = some q ∧ n ≤ (Λ - lev v).toNat := by
  unfold mergeChoices at hq
  split at hq
  · cases hm : firstMeeting Q b a Δ₀ u v Λ with
    | none => simp [hm] at hq
    | some i =>
      cases hg : checkedPath Q b (mergeStream b a Δ₀ u v Λ) i with
      | none => simp [hm, hg] at hq
      | some qGreedy =>
        simp only [hm, hg, Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact ⟨_, i, hg, firstMeeting_le hm⟩
        · split at hq
          · exact ⟨_, _, Option.mem_toFinset.mp hq, Nat.sub_le _ _⟩
          · simp at hq
  · simp at hq

private theorem pathFamily_mem_stream {a cstar A R C₁ : ℝ} {m : ℕ → ℕ}
    {k K₁ K₃ : ℕ} {b : Lattice → Bool} {q : PackedPath}
    (hq : q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b) :
    ∃ j ∈ scales (m k), ∃ y n,
      checkedPath (workingRegion a A R C₁ m k) b y n = some q ∧
      (n : ℝ) ≤ 8 * max 0 (cstar * ((j : ℝ) ^ 2 * (width k j : ℝ))) +
        ((trimLength (slopeCutoff a) K₁ K₃ + 1 : ℕ) : ℝ) := by
  unfold pathFamily at hq
  dsimp only at hq
  obtain ⟨u, -, hu⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨j, hj, hs⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨I, -, hI⟩ := Finset.mem_biUnion.mp hs
  let B := cstar * ((j : ℝ) ^ 2 * (width k j : ℝ))
  let l := mesh (m k) j
  let w := width k j
  let r := trimLength (slopeCutoff a) K₁ K₃
  let Q := workingRegion a A R C₁ m k
  refine ⟨j, hj, ?_⟩
  by_cases hfine : (l : ℝ) < 8 * B
  · -- A covered fine interval contributes its full mesh segment.
    rw [ite_eq_left hfine] at hI
    have hB : 8 * B ≤ 8 * max 0 B := mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
    exact ⟨_, l, fineChoice_checked (Option.mem_toFinset.mp hI),
      (hfine.le.trans hB).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))⟩
  · -- Each coarse piece fits between a grid level and its trimming window.
    rw [ite_eq_right hfine] at hI
    obtain ⟨h, -, hh⟩ := Finset.mem_biUnion.mp hI
    obtain ⟨ν, -, hν⟩ := Finset.mem_biUnion.mp hh
    let m' := ⌈B⌉₊
    let c := coarseCrossingCentre a h w I m' (ν.val + 1)
    let left := I + (m' : ℤ)
    let right := I + (l : ℤ) - (m' : ℤ)
    have hB : 0 ≤ max 0 B := le_max_left _ _
    have hceiling : ((m' + r : ℕ) : ℝ) ≤ 8 * max 0 B + ((r + 1 : ℕ) : ℝ) := by
      have hm' : (m' : ℝ) ≤ (⌈max 0 B⌉₊ : ℕ) :=
        Nat.cast_le.mpr (Nat.ceil_mono (le_max_right _ _))
      have hceil := Nat.ceil_lt_add_one hB
      push_cast
      linarith only [hm', hceil, hB]
    rcases Finset.mem_union.mp hν with ha | hm
    · obtain ⟨v, hv, hvq⟩ := Finset.mem_biUnion.mp ha
      have hwin := (trimWindow_spec a w left r c).1 v |>.mp (Finset.mem_filter.mp hv).1
      have hlen : (lev v - I).toNat ≤ m' + r := by
        have hupp := hwin.2.1
        dsimp only [left] at hupp
        omega
      exact ⟨_, _, arrivalChoice_checked (Option.mem_toFinset.mp hvq),
        (Nat.cast_le.mpr hlen).trans hceiling⟩
    · obtain ⟨v, hv, hvq⟩ := Finset.mem_biUnion.mp hm
      have hwin := (trimWindow_spec a w (right - (r : ℤ)) r c).1 v |>.mp
        (Finset.mem_filter.mp hv).1
      obtain ⟨y, n, hy, hn⟩ := mergeChoices_checked hvq
      have hlen : (I + (l : ℤ) - lev v).toNat ≤ m' + r := by
        have hlow := hwin.1
        dsimp only [right] at hlow
        omega
      exact ⟨y, n, hy, (Nat.cast_le.mpr (hn.trans hlen)).trans hceiling⟩

/-- Every path in the family of Appendix B, item (U5), stays in the actual working
region and collects no very bad vertex, for every Boolean mask
(Appendix B, item `ch:family`). -/
theorem pathFamily_region_mask {a cstar A R C₁ : ℝ} {m : ℕ → ℕ} {k K₁ K₃ : ℕ}
    {b : Lattice → Bool} {q : PackedPath}
    (hq : q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b) :
    (∀ i, q.2.2.vertex i ∈ workingRegion a A R C₁ m k) ∧
      (∀ z ∈ q.2.2.collectedSites, b z = false) := by
  obtain ⟨_, -, _, _, hchecked, -⟩ := pathFamily_mem_stream hq
  obtain ⟨hregion, hmask⟩ := checkedPath_region_mask hchecked
  refine ⟨hregion, fun z hz => ?_⟩
  obtain ⟨i, rfl⟩ := (q.2.2.mem_collectedSites_iff z).1 hz
  exact hmask i

private theorem scale_le {mk k j : ℕ} (hm : mk ≤ 3 * k) (hj : j ∈ scales mk) :
    1 ≤ j ∧ j ≤ k := by
  obtain ⟨hj₀, hj₁⟩ := Finset.mem_Icc.mp hj
  have hjstar := (grid_jstar_bounds (m := mk) rfl).2
  exact ⟨hj₀, by omega⟩

private theorem scales_card_le {mk k : ℕ} (hm : mk ≤ 3 * k) : (scales mk).card ≤ k := by
  have hsub : scales mk ⊆ Finset.Icc 1 k := fun _ hj => Finset.mem_Icc.mpr (scale_le hm hj)
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub

private theorem width_le_half {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    (width k j : ℝ) ≤ (2 : ℝ) ^ k / 2 := by
  have hp : (2 : ℝ) ^ (k - j + 1) ≤ (2 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ] at hp
  simp only [width, Nat.cast_pow, Nat.cast_ofNat]
  linarith

private theorem pathFamily_length_eventually {a cstar A R C₁ : ℝ}
    (m : ℕ → ℕ) (K₁ K₃ : ℕ) (hcstar : 0 < cstar) :
    ∀ᶠ k in atTop, m k ≤ 3 * k →
      ∀ b q, q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b →
        ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k := by
  let r := trimLength (slopeCutoff a) K₁ K₃
  have hr : ∀ᶠ k : ℕ in atTop, ((r + 1 : ℕ) : ℝ) / (4 * cstar) ≤ (2 : ℝ) ^ k :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (1 : ℕ), hr] with k hk hrk hm b q hq
  obtain ⟨j, hj, _, n, hchecked, hlen⟩ := pathFamily_mem_stream hq
  have hB : 0 ≤ cstar * ((j : ℝ) ^ 2 * (width k j : ℝ)) := by positivity
  rw [max_eq_right hB] at hlen
  rw [(checkedPath_spec hchecked).2.2.1]
  obtain ⟨hj₀, hjk⟩ := scale_le hm hj
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkSq : 1 ≤ (k : ℝ) ^ 2 := one_le_pow₀ hkR
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hr' : ((r + 1 : ℕ) : ℝ) ≤ 4 * cstar * (2 : ℝ) ^ k := by
    rw [mul_comm (4 * cstar)]
    exact (div_le_iff₀ (by positivity)).mp hrk
  have hr'' : ((r + 1 : ℕ) : ℝ) ≤ 4 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k := by
    refine hr'.trans ?_
    calc
      _ = 4 * cstar * 1 * (2 : ℝ) ^ k := by rw [mul_one]
      _ ≤ _ := by gcongr
  have hscale : 8 * (cstar * ((j : ℝ) ^ 2 * (width k j : ℝ))) ≤
      4 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k := by
    calc
      _ ≤ 8 * (cstar * ((k : ℝ) ^ 2 * ((2 : ℝ) ^ k / 2))) := by
        gcongr
        exact width_le_half hj₀ hjk
      _ = _ := by ring
  calc
    (n : ℝ) ≤ _ := hlen
    _ ≤ _ := add_le_add hscale hr''
    _ = _ := by ring

private theorem card_biUnion_mul_le {α β : Type*} [DecidableEq β] {s : Finset α}
    {f : α → Finset β} {B : ℝ} (h : ∀ x ∈ s, ((f x).card : ℝ) ≤ B) :
    ((s.biUnion f).card : ℝ) ≤ (s.card : ℝ) * B := by
  calc
    _ ≤ ∑ x ∈ s, ((f x).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ s, B := Finset.sum_le_sum h
    _ = _ := by simp

private theorem card_filter_biUnion_mul_le {α β : Type*} [DecidableEq β] {s : Finset α}
    {p : α → Prop} [DecidablePred p] {f : α → Finset β} {C B : ℝ}
    (hcard : (s.card : ℝ) ≤ C) (hB : 0 ≤ B) (h : ∀ x, ((f x).card : ℝ) ≤ B) :
    (((s.filter p).biUnion f).card : ℝ) ≤ C * B := by
  refine (card_biUnion_mul_le (fun x _ => h x)).trans (mul_le_mul_of_nonneg_right ?_ hB)
  have hfilter : ((s.filter p).card : ℝ) ≤ s.card := by exact_mod_cast Finset.card_filter_le _ _
  exact hfilter.trans hcard

private theorem card_option_le {α : Type*} (o : Option α) : (o.toFinset.card : ℝ) ≤ 1 := by
  cases o <;> simp

private theorem mergeChoices_card_le (Q : Set Lattice) (b : Lattice → Bool) (a : ℝ)
    (Δ₀ : ℕ) (u v : Lattice) (I Λ : ℤ) :
    ((mergeChoices Q b a Δ₀ u v I Λ).card : ℝ) ≤ 2 := by
  unfold mergeChoices
  split
  · cases firstMeeting Q b a Δ₀ u v Λ with
    | none => simp
    | some i =>
      cases hg : checkedPath Q b (mergeStream b a Δ₀ u v Λ) i with
      | none => simp [hg]
      | some q =>
        simp only [hg]
        let t := if gammaDefined Q b a u Λ then
          (checkedPath Q b (gammaStream b a u (lev v + (i : ℤ))) ((Λ - lev v).toNat - i)).toFinset
          else ∅
        have ht : (t.card : ℝ) ≤ 1 := by
          dsimp only [t]
          split
          · exact card_option_le _
          · simp
        have hinsert : ((insert q t).card : ℝ) ≤ (t.card : ℝ) + 1 := by
          exact_mod_cast Finset.card_insert_le q t
        exact hinsert.trans (by linarith only [ht])
  · simp

private theorem workingRegion_card_bound {a A R C₁ : ℝ} (m : ℕ → ℕ)
    (hA : 0 < A) (hR : 0 < R) (hC₁ : 0 ≤ C₁) {k : ℕ} (hm : m k ≤ 3 * k) :
    ((regionSites a A R C₁ m k).card : ℝ) ≤
      ((2 * (A + 5) + 3) * (2 * (R + 2 * C₁ + 10) + 5)) * ((2 : ℝ) ^ k) ^ 4 := by
  let s := (2 : ℝ) ^ k
  let B := R + 2 * C₁ + 10
  have hB : 0 < B := by dsimp [B]; positivity
  have hs : 1 ≤ s := one_le_pow₀ (by norm_num)
  have hs₃ : 1 ≤ s ^ 3 := one_le_pow₀ hs
  have hL : (2 : ℝ) ^ m k ≤ s ^ 3 := by
    rw [show s ^ 3 = (2 : ℝ) ^ (k * 3) by simp only [s, pow_mul]]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hlevel : 2 * ((A + 5) * (2 : ℝ) ^ m k) + 3 ≤ (2 * (A + 5) + 3) * s ^ 3 :=
    by linarith only [mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * (A + 5) by positivity), hs₃]
  have htransverse : 2 * (B * s) + 5 ≤ (2 * B + 5) * s := by linarith only [hs]
  have hbox := (boxS_finite_ncard_le a ((A + 5) * (2 : ℝ) ^ m k) (B * s)
    (by positivity) (by positivity)).2
  unfold regionSites
  rw [← Set.ncard_eq_toFinset_card _ (workingRegion_finite a A R C₁ m k)]
  calc
    _ ≤ (2 * ((A + 5) * (2 : ℝ) ^ m k) + 3) * (2 * (B * s) + 5) := hbox
    _ ≤ ((2 * (A + 5) + 3) * s ^ 3) * ((2 * B + 5) * s) := by
      exact mul_le_mul hlevel htransverse (by positivity) (by positivity)
    _ = _ := by change _ = ((2 * (A + 5) + 3) * (2 * B + 5)) * s ^ 4; ring

private theorem pathFamily_card_polynomial {a cstar A R C₁ : ℝ}
    (m : ℕ → ℕ) (K₁ K₃ : ℕ) (hA : 0 < A) (hR : 0 < R) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, ∀ k, m k ≤ 3 * k → ∀ b,
      ((pathFamily a cstar A R C₁ m k K₁ K₃ b).card : ℝ) ≤
        C * (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 10 := by
  let r := trimLength (slopeCutoff a) K₁ K₃
  let Cq := (2 * (A + 5) + 3) * (2 * (R + 2 * C₁ + 10) + 5)
  let Cg := 4 * (A + 4) + 1
  let Ch := 2 * R + 2
  let Cw := ((r + 1 : ℕ) : ℝ) * 17
  refine ⟨Cq * Cg * Ch * (4 * Cw), fun k hm b => ?_⟩
  let s := (2 : ℝ) ^ k
  let T := Cw * s
  have hs : 1 ≤ s := one_le_pow₀ (by norm_num)
  have hCh : 1 ≤ Ch := by dsimp [Ch]; linarith only [hR]
  have hT : 1 ≤ T := by
    have hr : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ r + 1 by omega)
    change (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * 17 * s
    calc
      1 = (1 : ℝ) * 1 * 1 := by norm_num
      _ ≤ ((r + 1 : ℕ) : ℝ) * 17 * s :=
        mul_le_mul (mul_le_mul hr (by norm_num) zero_le_one (by positivity))
          hs (by positivity) (by positivity)
  -- Count the actual grid levels, bins, and sites in either trimming window.
  have hgrid (j : ℕ) (hjk : j ≤ k) : ((gridLevels A (m k) j).card : ℝ) ≤ Cg * s ^ 4 := by
    refine (grid_count_le hA (m k) j _ (fun _ => mem_gridLevels)).2.trans ?_
    rw [show s ^ 4 = (2 : ℝ) ^ (k * 4) by simp only [s, pow_mul]]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega))
      (by positivity)
  have hbins (j : ℕ) (hjk : j ≤ k) : ((gridBins R k j).card : ℝ) ≤ Ch * s := by
    have hmem (h : ℤ) : h ∈ gridBins R k j ↔ ∃ x : ℝ, (h : ℝ) * 2 ^ (k - j) ≤ x ∧
        x < ((h : ℝ) + 1) * 2 ^ (k - j) ∧ |x| ≤ R * 2 ^ k := by
      simpa only [width, Nat.cast_pow, Nat.cast_ofNat] using (mem_gridBins (h := h) hR.le)
    exact (grid_bin_count_le hR hjk _ hmem).2.trans <|
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hjk) (by linarith only [hCh])
  have hwindow (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) (I : ℤ) (c : Lattice) :
      ((trimWindow a (width k j) I r c).card : ℝ) ≤ T := by
    have hw := width_le_half hj hjk
    have hwidth : 16 * (width k j : ℝ) + 2 ≤ 17 * s := by
      change 1 ≤ (2 : ℝ) ^ k at hs
      change _ ≤ 17 * (2 : ℝ) ^ k
      linarith only [hw, hs]
    calc
      _ ≤ ((r + 1 : ℕ) : ℝ) * (16 * (width k j : ℝ) + 2) := (trimWindow_spec a _ I r c).2
      _ ≤ ((r + 1 : ℕ) : ℝ) * (17 * s) := mul_le_mul_of_nonneg_left hwidth (Nat.cast_nonneg _)
      _ = T := by dsimp only [T, Cw]; ring
  -- Sum the path counts over sites, scales, grid levels, bins, and rounded blocks.
  unfold pathFamily
  dsimp only
  calc
    _ ≤ ((regionSites a A R C₁ m k).card : ℝ) *
        ((k : ℝ) * ((Cg * s ^ 4) * ((Ch * s) * ((k : ℝ) ^ 2 * (4 * T))))) := by
      apply card_biUnion_mul_le
      intro u _
      refine (card_biUnion_mul_le ?_).trans (mul_le_mul_of_nonneg_right ?_ ?_)
      · intro j hj
        obtain ⟨hj₀, hjk⟩ := scale_le hm hj
        have hk : (1 : ℝ) ≤ k := by exact_mod_cast (hj₀.trans hjk)
        refine (card_biUnion_mul_le ?_).trans <|
          mul_le_mul_of_nonneg_right (hgrid j hjk) (by positivity)
        intro I _
        split
        · -- A fine cell has at most one selected segment.
          refine (card_option_le _).trans ?_
          calc
            1 = (1 * 1 : ℝ) * (1 ^ 2 * (1 * 1)) := by norm_num
            _ ≤ _ := by
              gcongr
              norm_num
        · -- Each left-window site gives at most one arrival, and each right-window
          -- site gives at most a greedy prefix and a staircase suffix.
          refine card_filter_biUnion_mul_le (hbins j hjk) (by positivity) ?_
          intro h
          refine (card_biUnion_mul_le ?_).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
          · intro ν _
            let w := width k j
            let l := mesh (m k) j
            let m' := ⌈cstar * ((j : ℝ) ^ 2 * (w : ℝ))⌉₊
            let c := coarseCrossingCentre a h w I m' (ν.val + 1)
            let left := I + (m' : ℤ)
            let right := I + (l : ℤ) - (m' : ℤ)
            have hsum (S U : Finset PackedPath) :
                ((S ∪ U).card : ℝ) ≤ (S.card : ℝ) + (U.card : ℝ) := by
              exact_mod_cast Finset.card_union_le S U
            refine (hsum _ _).trans ((add_le_add ?_ ?_).trans
              (show T * 1 + T * 2 ≤ 4 * T by linarith only [hT]))
            · exact card_filter_biUnion_mul_le (hwindow j hj₀ hjk left c) zero_le_one
                (fun _ => card_option_le _)
            · exact card_filter_biUnion_mul_le (hwindow j hj₀ hjk (right - (r : ℤ)) c)
                (by norm_num) (fun _ => mergeChoices_card_le _ _ _ _ _ _ _ _)
          · rw [Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
            exact pow_le_pow_left₀ (Nat.cast_nonneg j) (by exact_mod_cast hjk) _
      · exact_mod_cast scales_card_le hm
      · positivity
    _ ≤ (Cq * s ^ 4) *
        ((k : ℝ) * ((Cg * s ^ 4) * ((Ch * s) * ((k : ℝ) ^ 2 * (4 * T))))) :=
      mul_le_mul_of_nonneg_right (workingRegion_card_bound m hA hR hC₁ hm) (by positivity)
    _ = _ := by dsimp only [T, s]; ring

/-- At large record scales, the actual family in Appendix B, item (U5), has at
most `s_k^11` paths of length at most `8 cstar k^2 s_k`, for every Boolean mask
(Appendix B, item `ch:family`). -/
theorem pathFamily_bounds_eventually {a cstar A R C₁ : ℝ}
    (m : ℕ → ℕ) (K₁ K₃ : ℕ) (hA : 0 < A) (hR : 0 < R) (hC₁ : 0 ≤ C₁)
    (hcstar : 0 < cstar) :
    ∀ᶠ k in atTop, m k ≤ 3 * k →
      (∀ b, ((pathFamily a cstar A R C₁ m k K₁ K₃ b).card : ℝ) ≤ ((2 : ℝ) ^ k) ^ 11) ∧
      (∀ b q, q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ b →
        ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k) := by
  obtain ⟨C, hcard⟩ := pathFamily_card_polynomial (a := a) (cstar := cstar) m K₁ K₃ hA hR hC₁
  -- The fixed multiplicative constant and the cubic polynomial are absorbed by one power of s_k.
  have hlim : Tendsto (fun k : ℕ => C * ((k : ℝ) ^ 3 / (2 : ℝ) ^ k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hlim.eventually_lt_const zero_lt_one,
    pathFamily_length_eventually (a := a) (A := A) (R := R) (C₁ := C₁) m K₁ K₃ hcstar]
    with k hpoly hlen hm
  refine ⟨fun b => (hcard k hm b).trans ?_, hlen hm⟩
  have hsmall : C * (k : ℝ) ^ 3 ≤ (2 : ℝ) ^ k := by
    have hratio : C * (k : ℝ) ^ 3 / (2 : ℝ) ^ k ≤ 1 := by
      simpa only [mul_div_assoc] using hpoly.le
    have hpow := (div_le_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ k by positivity)).mp hratio
    simpa only [one_mul] using hpow
  rw [pow_succ' ((2 : ℝ) ^ k) 10]
  exact mul_le_mul_of_nonneg_right hsmall (by positivity)

end LPPDifferentiability.SelectedGridPaths
