/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.StageSplitWitnesses
public import Differentiability.Model.StageItinerarySteps
public import Differentiability.Model.ExcessBlockGeometry
import Mathlib.Tactic

/-! The closed geometry of a stage, the split witnesses of a stage (Lemma B.8 of the
differentiability preprint) and witness-free full stages (Lemma 6.3 of the same preprint). -/

public section

open scoped BigOperators

namespace LPPDifferentiability

/-- A stage starting at any local time `k`, with no cut strictly before `l`, has
length at most `2m`, stays within transverse distance `s+1` of its start, and lies
in the block at its index (Section 6.3 of the differentiability preprint). -/
theorem Path.stage_closed_geometry {d : ℕ × ℕ} (p : Path 0 d) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (m : ℕ) (hm : 1 ≤ m) (s : ℝ) (hs : 2 ≤ s) (k l : Fin (d.1+d.2+1)) (hkl : k ≤ l)
    (hmin : ∀ t, k < t → t < l → t.val-k.val < 2*m ∧
      |((1-a)*(p.vertex t).1-a*(p.vertex t).2)-((1-a)*(p.vertex k).1-a*(p.vertex k).2)| < s) :
    l.val-k.val ≤ 2*m ∧ ∀ t, k ≤ t → t ≤ l →
      |((1-a)*(p.vertex t).1-a*(p.vertex t).2)-((1-a)*(p.vertex k).1-a*(p.vertex k).2)| ≤ s+1 ∧
      ((⌊(k.val : ℝ)/(m : ℝ)⌋ : ℤ) : ℝ)*(m : ℝ) ≤ ((p.vertex t).1 : ℝ)+((p.vertex t).2 : ℝ) ∧
      ((p.vertex t).1 : ℝ)+((p.vertex t).2 : ℝ) ≤ ((⌊(k.val : ℝ)/(m : ℝ)⌋ : ℤ) : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
      |(1-a)*((p.vertex t).1 : ℝ)-a*((p.vertex t).2 : ℝ)-
        ((⌊((1-a)*(p.vertex k).1-a*(p.vertex k).2)/s⌋ : ℤ) : ℝ)*s| ≤ 4*s := by
  obtain ⟨hlen, hgeo⟩ := interval_geometry p a ha ha1 m hm s hs k l hkl hmin
  refine ⟨hlen, fun t hkt htl => ?_⟩
  have hkl' : k.val ≤ l.val := hkl
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsR : 0 < s := by linarith
  have hd := (Nat.cast_le (α := ℝ)).mpr hlen
  rw [Nat.cast_sub hkl', Nat.cast_mul, Nat.cast_ofNat] at hd
  have hktR : (k.val : ℝ) ≤ t.val := by exact_mod_cast hkt
  have htlR : (t.val : ℝ) ≤ l.val := by exact_mod_cast htl
  have hlev := p.level t
  simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at hlev
  have hlevR : ((p.vertex t).1 : ℝ)+((p.vertex t).2 : ℝ) = t.val := by exact_mod_cast hlev
  have hkfloor := floor_window (k.val : ℝ) m hmR
  have hrfloor := floor_window ((1-a)*(p.vertex k).1-a*(p.vertex k).2) s hsR
  have htbound := abs_le.mp (hgeo t hkt htl)
  refine ⟨hgeo t hkt htl, by linarith, by nlinarith, ?_⟩
  apply abs_le.mpr
  constructor <;> linarith


/-- Lemma 6.5 and Lemma B.8 of the differentiability preprint, for one stage: the greedy split
segments are defect witnesses of the stage's block with pairwise disjoint collected sites, and the
stage defect is at least `-ηs - 2ηs M` minus the total excess of the stage's collected sites. -/
theorem Path.stage_split_witnesses {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 1 ≤ m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr M0 : ℝ) (hη : 0 < η)
    (hstep : |G0| + |(dl+dr)/2| + M0 ≤ η*s/2)
    (k l : Fin (d.1+d.2+1)) (hkl : k ≤ l)
    (hmin : ∀ t, k < t → t < l → t.val-k.val < 2*m ∧
      |((1-a)*(p.vertex t).1-a*(p.vertex t).2)-((1-a)*(p.vertex k).1-a*(p.vertex k).2)| < s) :
    let b : Lattice := (⌊(k.val : ℝ)/(m : ℝ)⌋, ⌊((1-a)*(p.vertex k).1-a*(p.vertex k).2)/s⌋)
    let segment : ℕ → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun k0 _ e q =>
      k0+(e.1+e.2) ≤ d.1+d.2 ∧
        ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)), t.val = k0+i.val → q.vertex i = p.vertex t
    let block : Lattice → Lattice → Prop := fun b z =>
      (b.1 : ℝ)*(m : ℝ) ≤ (z.1 : ℝ)+(z.2 : ℝ) ∧ (z.1 : ℝ)+(z.2 : ℝ) ≤ (b.1 : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
        |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ)-(b.2 : ℝ)*s| ≤ 4*s
    let defectWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun b _ e q =>
      (∀ i, block b (q.vertex i)) ∧
        min (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q)
          (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q) < -(η*s)
    ∃ M : ℕ, ∃ time : Fin M → ℕ, ∃ start : Fin M → Lattice, ∃ displacement : Fin M → ℕ × ℕ,
      ∃ paths : (j : Fin M) → Path (start j) (displacement j),
      (∀ j, k.val ≤ time j ∧ time j+((displacement j).1+(displacement j).2) ≤ l.val ∧
        segment (time j) (start j) (displacement j) (paths j) ∧
        defectWitness b (start j) (displacement j) (paths j)) ∧
      (∀ j j', j ≠ j' → Disjoint (paths j).collectedSites (paths j').collectedSites) ∧
      ∀ (u : Lattice) (e : ℕ × ℕ) (y : Path u e), segment k.val u e y → k.val+(e.1+e.2) = l.val →
        -(η*s)-2*η*s*(M : ℝ)-∑ z ∈ y.collectedSites, max (ω z-M0) 0 ≤
          G0*((e.1 : ℝ)+(e.2 : ℝ))+((dl+dr)/2)*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y := by
  intro b segment block defectWitness
  obtain ⟨_, hgeo⟩ := p.stage_closed_geometry a ha ha1 m hm s hs k l hkl hmin
  have hlt := l.isLt
  have hc0 : (0 : ℝ) ≤ η*s := mul_nonneg hη.le (by linarith)
  obtain ⟨F, hF, hFdisj, hFb⟩ :=
    p.stage_greedy_windows ω a ha ha1 s η G0 dl dr M0 hc0 hstep k l hkl
  have hseg : ∀ j : Fin F.card, ∃ t : ℕ, ∃ u : Lattice, ∃ e : ℕ × ℕ, ∃ y : Path u e,
      (k.val ≤ t ∧ t+(e.1+e.2) ≤ l.val ∧ segment t u e y ∧ defectWitness b u e y) ∧
      (t = (F.equivFin.symm j).1.1 ∧ t+(e.1+e.2) = (F.equivFin.symm j).1.2) := by
    intro j
    have hwmem := (F.equivFin.symm j).2
    generalize (F.equivFin.symm j).1 = w at hwmem ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hF w hwmem
    obtain ⟨e, y, hy, hyl⟩ :=
      p.exists_segment ⟨w.1, by omega⟩ ⟨w.2, by omega⟩ (show w.1 ≤ w.2 by omega)
    have hyl' : w.1+(e.1+e.2) = w.2 := hyl
    have hy' : w.1+(e.1+e.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)),
        t.val = w.1+i.val → y.vertex i = p.vertex t := hy
    have hblock : ∀ i, block b (y.vertex i) := by
      intro i
      obtain ⟨t, ht, hyt⟩ := p.segment_vertex y w.1 hy' i
      have hi := i.isLt
      rw [hyt]
      exact (hgeo t (show k.val ≤ t.val by omega) (show t.val ≤ l.val by omega)).2
    have havg := h4 _ e y hy' hyl'
    have hmn1 := min_le_left
      (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y)
      (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y)
    have hmn2 := min_le_right
      (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y)
      (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y)
    have hlt' : min (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y)
        (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y) < -(η*s) := by
      linarith
    exact ⟨w.1, _, e, y, ⟨h1, by omega, hy', And.intro hblock hlt'⟩, rfl, hyl'⟩
  choose time start displacement paths hpaths using hseg
  refine ⟨F.card, time, start, displacement, paths, fun j => (hpaths j).1, ?_,
    fun u e y hy hyl => hFb u e y hy hyl⟩
  intro j j' hjj'
  have hne : (F.equivFin.symm j).1 ≠ (F.equivFin.symm j').1 :=
    fun h => hjj' (F.equivFin.symm.injective (Subtype.ext h))
  obtain ⟨⟨_, _, hs1, _⟩, ht1, he1⟩ := hpaths j
  obtain ⟨⟨_, _, hs2, _⟩, ht2, he2⟩ := hpaths j'
  rcases hFdisj _ (F.equivFin.symm j).2 _ (F.equivFin.symm j').2 hne with h | h
  · exact p.segment_collectedSites_disjoint (paths j) (paths j') (time j) (time j') hs1 hs2
      (by omega)
  · exact (p.segment_collectedSites_disjoint (paths j') (paths j) (time j') (time j) hs2 hs1
      (by omega)).symm

/-- Lemma 6.3 of the differentiability preprint: a full stage none of whose segments
witnesses either event of its block has both extreme defects at least `-ηs`, and
average defect at least `ηs` when its cut is longitudinal. -/
theorem Path.witness_free_stage_defect {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 1 ≤ m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K : ℝ)
    (hK : 3*η*s+|(dl+dr)/2| * (2*s+2) < K*s)
    (k l : Fin (d.1+d.2+1)) (hkl : k < l)
    (hcut : 2*m ≤ l.val-k.val ∨
      s ≤ |((1-a)*(p.vertex l).1-a*(p.vertex l).2)-((1-a)*(p.vertex k).1-a*(p.vertex k).2)|)
    (hmin : ∀ t, k < t → t < l → t.val-k.val < 2*m ∧
      |((1-a)*(p.vertex t).1-a*(p.vertex t).2)-((1-a)*(p.vertex k).1-a*(p.vertex k).2)| < s) :
    let b : Lattice := (⌊(k.val : ℝ)/(m : ℝ)⌋, ⌊((1-a)*(p.vertex k).1-a*(p.vertex k).2)/s⌋)
    let v : Lattice → Lattice := fun b =>
      let j : ℤ := ⌊(b.2:ℝ)*s+a*((b.1*m:ℤ):ℝ)⌋
      (j,b.1*m-j)
    let segment : ℕ → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun k0 _ e q =>
      k0+(e.1+e.2) ≤ d.1+d.2 ∧
        ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)), t.val = k0+i.val → q.vertex i = p.vertex t
    let block : Lattice → Lattice → Prop := fun b z =>
      (b.1 : ℝ)*(m : ℝ) ≤ (z.1 : ℝ)+(z.2 : ℝ) ∧ (z.1 : ℝ)+(z.2 : ℝ) ≤ (b.1 : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
        |(1-a)*(z.1 : ℝ)-a*(z.2 : ℝ)-(b.2 : ℝ)*s| ≤ 4*s
    let defectWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop := fun b _ e q =>
      (∀ i, block b (q.vertex i)) ∧
        min (G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q)
          (G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω q) < -(η*s)
    let crossingWitness : Lattice → (u : Lattice) → (e : ℕ × ℕ) → Path u e → Prop :=
      fun b u e q =>
        u.1+u.2 = (b.1+1)*m ∧ e.1+e.2 = m ∧
          (∀ i, |((1-a)*((q.vertex i).1 : ℝ)-a*((q.vertex i).2 : ℝ))-
            ((1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ))| ≤ 8*s) ∧
          G0*(m : ℝ)-K*s < pathWeight ω q
    (∀ (t : ℕ) (u : Lattice) (e : ℕ × ℕ) (y : Path u e), k.val ≤ t → t+(e.1+e.2) ≤ l.val →
        segment t u e y → ¬ defectWitness b u e y ∧ ¬ crossingWitness b u e y) →
    ∀ (u : Lattice) (e : ℕ × ℕ) (y : Path u e), segment k.val u e y → k.val+(e.1+e.2) = l.val →
      -(η*s) ≤ G0*((e.1 : ℝ)+(e.2 : ℝ))+dl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y ∧
      -(η*s) ≤ G0*((e.1 : ℝ)+(e.2 : ℝ))+dr*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y ∧
      (|((1-a)*(p.vertex l).1-a*(p.vertex l).2)-((1-a)*(p.vertex k).1-a*(p.vertex k).2)| < s →
        η*s ≤ G0*((e.1 : ℝ)+(e.2 : ℝ))+((dl+dr)/2)*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y) := by
  intro b v segment block defectWitness crossingWitness hfree u e y hy hyl
  obtain ⟨hlen, hgeo⟩ := p.stage_closed_geometry a ha ha1 m hm s hs k l hkl.le hmin
  have hkl' : k.val < l.val := hkl
  have hlt := l.isLt
  have hsR : (0 : ℝ) < s := by linarith
  -- Step W1: every segment of the stage has both extreme defects at least `-ηs`.
  have hW1 : ∀ (t : ℕ) (u' : Lattice) (e' : ℕ × ℕ) (y' : Path u' e'), k.val ≤ t →
      t+(e'.1+e'.2) ≤ l.val → segment t u' e' y' →
      -(η*s) ≤ G0*((e'.1 : ℝ)+(e'.2 : ℝ))+dl*((1-a)*(e'.1 : ℝ)-a*(e'.2 : ℝ))-pathWeight ω y' ∧
      -(η*s) ≤ G0*((e'.1 : ℝ)+(e'.2 : ℝ))+dr*((1-a)*(e'.1 : ℝ)-a*(e'.2 : ℝ))-pathWeight ω y' := by
    intro t u' e' y' h1 h2 hy'
    have hy'' : t+(e'.1+e'.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e'.1+e'.2+1)) (t' : Fin (d.1+d.2+1)),
        t'.val = t+i.val → y'.vertex i = p.vertex t' := hy'
    have hblock : ∀ i, block b (y'.vertex i) := by
      intro i
      obtain ⟨t', ht', hyt⟩ := p.segment_vertex y' t hy'' i
      have hi := i.isLt
      rw [hyt]
      exact (hgeo t' (show k.val ≤ t'.val by omega) (show t'.val ≤ l.val by omega)).2
    have hm' : -(η*s) ≤
        min (G0*((e'.1 : ℝ)+(e'.2 : ℝ))+dl*((1-a)*(e'.1 : ℝ)-a*(e'.2 : ℝ))-pathWeight ω y')
          (G0*((e'.1 : ℝ)+(e'.2 : ℝ))+dr*((1-a)*(e'.1 : ℝ)-a*(e'.2 : ℝ))-pathWeight ω y') := by
      by_contra hneg
      exact (hfree t u' e' y' h1 h2 hy').1 (And.intro hblock (not_le.mp hneg))
    exact ⟨hm'.trans (min_le_left _ _), hm'.trans (min_le_right _ _)⟩
  have hstage := hW1 k.val u e y le_rfl hyl.le hy
  refine ⟨hstage.1, hstage.2, fun hlong => ?_⟩
  -- Step W2: a longitudinal cut has length `2m`; the crossing levels lie in the stage.
  have hl2 : l.val = k.val+2*m := by
    rcases hcut with h | h
    · omega
    · exact absurd h (not_le.mpr hlong)
  by_contra hneg
  rw [not_le] at hneg
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hP := floor_window (k.val : ℝ) m hmR
  have hP0 : 0 ≤ ⌊(k.val : ℝ)/(m : ℝ)⌋ :=
    Int.floor_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) hmR.le)
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = ⌊(k.val : ℝ)/(m : ℝ)⌋ := ⟨_, Int.toNat_of_nonneg hP0⟩
  have hqR : ((⌊(k.val : ℝ)/(m : ℝ)⌋ : ℤ) : ℝ) = (q : ℝ) := by rw [← hq, Int.cast_natCast]
  rw [hqR] at hP
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = q*m := ⟨_, rfl⟩
  have hAR : (A : ℝ) = (q : ℝ)*(m : ℝ) := by rw [hA, Nat.cast_mul]
  have hA1 : A ≤ k.val := by
    have h : (A : ℝ) ≤ (k.val : ℝ) := by rw [hAR]; exact hP.1
    exact_mod_cast h
  have hA2 : k.val < A+m := by
    have h : (k.val : ℝ) < (A : ℝ)+(m : ℝ) := by rw [hAR]; linarith [hP.2]
    exact_mod_cast h
  obtain ⟨i1, hi1⟩ : ∃ i1 : Fin (d.1+d.2+1), i1.val = A+m := ⟨⟨A+m, by omega⟩, rfl⟩
  obtain ⟨i2, hi2⟩ : ∃ i2 : Fin (d.1+d.2+1), i2.val = A+2*m := ⟨⟨A+2*m, by omega⟩, rfl⟩
  obtain ⟨e1, y1, hy1, hl1⟩ := p.exists_segment k i1 (show k.val ≤ i1.val by omega)
  obtain ⟨e23, y23, hy23, hl23⟩ := p.exists_segment i1 l (show i1.val ≤ l.val by omega)
  obtain ⟨ec, yc, hyc, hlc⟩ := p.exists_segment i1 i2 (show i1.val ≤ i2.val by omega)
  obtain ⟨e3, y3, hy3, hl3⟩ := p.exists_segment i2 l (show i2.val ≤ l.val by omega)
  -- Step W3: additivity and W1 give `Hdef(crossing) < 3ηs`.
  have hadd1 := (p.segment_defect_add ω a G0 ((dl+dr)/2) 0 y y1 y23 k.val i1.val hy hy1 hy23
    hl1 (by omega)).1
  have hadd2 := (p.segment_defect_add ω a G0 ((dl+dr)/2) 0 y23 yc y3 i1.val i2.val hy23 hyc
    hy3 hlc (by omega)).1
  have hb1 := hW1 k.val _ e1 y1 le_rfl (by omega) hy1
  have hb3 := hW1 i2.val _ e3 y3 (by omega) (by omega) hy3
  -- Step W4: the crossing segment witnesses the crossing event.
  have hlenc : ec.1+ec.2 = m := by omega
  obtain ⟨_, hx, hyy⟩ := p.segment_endpoints yc i1.val hyc i1 i2 rfl hlc.symm
  have hxR : (ec.1 : ℝ) = ((p.vertex i2).1 : ℝ)-((p.vertex i1).1 : ℝ) := by exact_mod_cast hx
  have hyR : (ec.2 : ℝ) = ((p.vertex i2).2 : ℝ)-((p.vertex i1).2 : ℝ) := by exact_mod_cast hyy
  have hg1 := (hgeo i1 (show k.val ≤ i1.val by omega) (show i1.val ≤ l.val by omega)).1
  have hg2 := (hgeo i2 (show k.val ≤ i2.val by omega) (show i2.val ≤ l.val by omega)).1
  have hrc : |(1-a)*(ec.1 : ℝ)-a*(ec.2 : ℝ)| ≤ 2*s+2 := by
    rw [hxR, hyR]
    have h1 := abs_le.mp hg1
    have h2 := abs_le.mp hg2
    apply abs_le.mpr
    constructor <;> linarith
  have habs : -(|(dl+dr)/2| * (2*s+2)) ≤ (dl+dr)/2*((1-a)*(ec.1 : ℝ)-a*(ec.2 : ℝ)) := by
    have h1 : |(dl+dr)/2*((1-a)*(ec.1 : ℝ)-a*(ec.2 : ℝ))| ≤ |(dl+dr)/2| * (2*s+2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hrc (abs_nonneg _)
    linarith [neg_abs_le ((dl+dr)/2*((1-a)*(ec.1 : ℝ)-a*(ec.2 : ℝ)))]
  have hmc : G0*((ec.1 : ℝ)+(ec.2 : ℝ)) = G0*(m : ℝ) := by
    rw [show ((ec.1 : ℝ)+(ec.2 : ℝ)) = (m : ℝ) by exact_mod_cast hlenc]
  have hWc : G0*(m : ℝ)-K*s < pathWeight ω yc := by
    linarith [hb1.1, hb1.2, hb3.1, hb3.2]
  have hrk : ((b.2 : ℤ) : ℝ)*s ≤ (1-a)*((p.vertex k).1 : ℝ)-a*((p.vertex k).2 : ℝ) ∧
      (1-a)*((p.vertex k).1 : ℝ)-a*((p.vertex k).2 : ℝ) < (((b.2 : ℤ) : ℝ)+1)*s :=
    floor_window ((1-a)*(p.vertex k).1-a*(p.vertex k).2) s hsR
  have hcv : ((b.2 : ℤ) : ℝ)*s-1 < (1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ) ∧
      (1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ) ≤ ((b.2 : ℤ) : ℝ)*s := by
    obtain ⟨_, h1, h2⟩ := excess_block_center a s m (b.1+1) b.2
    exact ⟨h1, h2⟩
  have hband : ∀ i : Fin (ec.1+ec.2+1), |((1-a)*((yc.vertex i).1 : ℝ)-a*((yc.vertex i).2 : ℝ))-
      ((1-a)*((v (b.1+1,b.2)).1 : ℝ)-a*((v (b.1+1,b.2)).2 : ℝ))| ≤ 8*s := by
    intro i
    obtain ⟨t, ht, hyt⟩ := p.segment_vertex yc i1.val hyc i
    have hi := i.isLt
    rw [hyt]
    have hg := abs_le.mp (hgeo t (show k.val ≤ t.val by omega) (show t.val ≤ l.val by omega)).1
    apply abs_le.mpr
    constructor <;> linarith [hcv.1, hcv.2, hrk.1, hrk.2, hg.1, hg.2]
  have hlevel : (p.vertex i1).1+(p.vertex i1).2 = (b.1+1)*(m : ℤ) := by
    have h := p.level i1
    simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at h
    have hbq : b.1 = (q : ℤ) := hq.symm
    rw [h, hi1, hbq, hA]
    push_cast
    ring
  exact (hfree i1.val _ ec yc (by omega) (by omega) hyc).2
    (And.intro hlevel (And.intro hlenc (And.intro hband hWc)))

end LPPDifferentiability
