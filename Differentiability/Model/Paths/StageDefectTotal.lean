/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.WitnessFreeStage
public import Differentiability.Model.StageItinerarySteps
public import Differentiability.Model.Paths.DefectAlgebra
import Mathlib.Tactic

/-! Full stages under a corner (Lemma 6.8 of the differentiability preprint) and the total defect of
a path from the origin with one disjoint witness family ((B.18) of the same preprint). -/

public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Lemma 6.8 of the differentiability preprint with the excess from equation (B.13) and the
general-weight estimate of Lemma B.8 in Appendix B's "One-step bound" subsection: under
`c ≥ 2η`, every full stage has a family of disjoint witnesses of either type of its block with
`Hdef ≥ ηs - 4ηs|F|` minus the stage excess. -/
theorem Path.full_stage_defect {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 1 ≤ m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K M0 : ℝ) (hη : 0 < η) (hc : 2*η ≤ (dl-dr)/2)
    (hstep : |G0|+|(dl+dr)/2|+M0 ≤ η*s/2)
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
    ∃ M : ℕ, ∃ time : Fin M → ℕ, ∃ start : Fin M → Lattice, ∃ displacement : Fin M → ℕ × ℕ,
      ∃ paths : (j : Fin M) → Path (start j) (displacement j),
      (∀ j, k.val ≤ time j ∧ time j+((displacement j).1+(displacement j).2) ≤ l.val ∧
        segment (time j) (start j) (displacement j) (paths j) ∧
        (defectWitness b (start j) (displacement j) (paths j) ∨
          crossingWitness b (start j) (displacement j) (paths j))) ∧
      (∀ j j', j ≠ j' → Disjoint (paths j).collectedSites (paths j').collectedSites) ∧
      ∀ (u : Lattice) (e : ℕ × ℕ) (y : Path u e), segment k.val u e y → k.val+(e.1+e.2) = l.val →
        η*s-4*η*s*(M : ℝ)-∑ z ∈ y.collectedSites, max (ω z-M0) 0 ≤
          G0*((e.1 : ℝ)+(e.2 : ℝ))+((dl+dr)/2)*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y := by
  intro b v segment block defectWitness crossingWitness
  have hgap : dr ≤ dl := by linarith
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hηs : 0 ≤ η*s := mul_nonneg hη.le hs0
  obtain ⟨M, time, start, displacement, paths, hmem, hdisj, hbound⟩ :=
    p.stage_split_witnesses ω a ha ha1 m hm s hs η G0 dl dr M0 hη hstep k l hkl.le hmin
  have hZ : ∀ (u : Lattice) (e : ℕ × ℕ) (y : Path u e),
      0 ≤ ∑ z ∈ y.collectedSites, max (ω z-M0) 0 :=
    fun _ _ _ => Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    by_cases hw : ∃ (t : ℕ) (u' : Lattice) (e' : ℕ × ℕ) (y' : Path u' e'), k.val ≤ t ∧
        t+(e'.1+e'.2) ≤ l.val ∧ segment t u' e' y' ∧
          (defectWitness b u' e' y' ∨ crossingWitness b u' e' y')
    · -- The stage has a witness but no split segment: a family of one witness.
      obtain ⟨t, u', e', y', h1, h2, h3, h4⟩ := hw
      refine ⟨1, fun _ => t, fun _ => u', fun _ => e', fun _ => y', fun _ => ⟨h1, h2, h3, h4⟩,
        fun j j' h => absurd (Subsingleton.elim j j') h, fun u e y hy hyl => ?_⟩
      have h0 := hbound u e y hy hyl
      simp only [Nat.cast_one, Nat.cast_zero] at h0 ⊢
      linarith
    · -- Witness-free full stage: Lemma 6.3 and (2.15) of the differentiability preprint.
      have hfree := p.witness_free_stage_defect ω a ha ha1 m hm s hs η G0 dl dr K hK k l hkl
        hcut hmin (fun t u' e' y' h1 h2 h3 =>
          ⟨fun hd => hw ⟨t, u', e', y', h1, h2, h3, Or.inl hd⟩,
            fun hcr => hw ⟨t, u', e', y', h1, h2, h3, Or.inr hcr⟩⟩)
      refine ⟨0, time, start, displacement, paths,
        fun j => ⟨(hmem j).1, (hmem j).2.1, (hmem j).2.2.1, Or.inl (hmem j).2.2.2⟩, hdisj,
        fun u e y hy hyl => ?_⟩
      obtain ⟨hm1, hm2, hlong⟩ := hfree u e y hy hyl
      simp only [Nat.cast_zero]
      have hZy := hZ u e y
      by_cases hlg : |((1-a)*(p.vertex l).1-a*(p.vertex l).2)-
          ((1-a)*(p.vertex k).1-a*(p.vertex k).2)| < s
      · have := hlong hlg
        linarith
      · have hid := Path.path_defect_min_identity a G0 dl dr hgap ω y
        obtain ⟨_, hx, hy2⟩ := p.segment_endpoints y k.val hy k l rfl hyl.symm
        have hxR : (e.1 : ℝ) = ((p.vertex l).1 : ℝ)-((p.vertex k).1 : ℝ) := by exact_mod_cast hx
        have hyR : (e.2 : ℝ) = ((p.vertex l).2 : ℝ)-((p.vertex k).2 : ℝ) := by exact_mod_cast hy2
        have hr : (1-a)*(e.1 : ℝ)-a*(e.2 : ℝ) =
            ((1-a)*(p.vertex l).1-a*(p.vertex l).2)-((1-a)*(p.vertex k).1-a*(p.vertex k).2) := by
          rw [hxR, hyR]
          ring
        have hge : s ≤ |(1-a)*(e.1 : ℝ)-a*(e.2 : ℝ)| := by
          rw [hr]
          exact not_lt.mp hlg
        have hc' : (2*η)*s ≤ ((dl-dr)/2)*|(1-a)*(e.1 : ℝ)-a*(e.2 : ℝ)| :=
          mul_le_mul hc hge hs0 (by linarith)
        have hmn := le_min hm1 hm2
        linarith
  · -- At least one split segment: arithmetic as in the differentiability preprint.
    refine ⟨M, time, start, displacement, paths,
      fun j => ⟨(hmem j).1, (hmem j).2.1, (hmem j).2.2.1, Or.inl (hmem j).2.2.2⟩, hdisj,
      fun u e y hy hyl => ?_⟩
    have h1 := hbound u e y hy hyl
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
    have h2 : η*s*1 ≤ η*s*(M : ℝ) := mul_le_mul_of_nonneg_left hM1 hηs
    linarith

/-- The remainder clause of Lemma 6.8: every stage, the remainder included, has
`Hdef ≥ -ηs - 4ηs|F|` minus the stage excess, with `F` its split defect witnesses. -/
theorem Path.stage_defect_four_witnesses {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
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
        -(η*s)-4*η*s*(M : ℝ)-∑ z ∈ y.collectedSites, max (ω z-M0) 0 ≤
          G0*((e.1 : ℝ)+(e.2 : ℝ))+((dl+dr)/2)*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y := by
  intro b segment block defectWitness
  obtain ⟨M, time, start, displacement, paths, hmem, hdisj, hbound⟩ :=
    p.stage_split_witnesses ω a ha ha1 m hm s hs η G0 dl dr M0 hη hstep k l hkl hmin
  refine ⟨M, time, start, displacement, paths, hmem, hdisj, fun u e y hy hyl => ?_⟩
  have h1 := hbound u e y hy hyl
  have h2 : 0 ≤ η*s*(M : ℝ) := mul_nonneg (mul_nonneg hη.le (by linarith)) (Nat.cast_nonneg M)
  linarith

/-- Equation (B.18) of the differentiability preprint: for the actual first cuts of a path from the
origin, one family of witnesses of the stage events with pairwise disjoint collected sites, and
`Hdef(x_{0:n}) ≥ (N-1)ηs - 4ηs|F|` minus the total excess of the path. -/
theorem Path.total_defect_disjoint_witnesses {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 1 ≤ m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K M0 : ℝ) (hη : 0 < η) (hc : 2*η ≤ (dl-dr)/2)
    (hstep : |G0|+|(dl+dr)/2|+M0 ≤ η*s/2)
    (hK : 3*η*s+|(dl+dr)/2| * (2*s+2) < K*s) :
    let rho (t : Fin (d.1+d.2+1)) : ℝ := (1-a)*(p.vertex t).1-a*(p.vertex t).2
    let pi (t : Fin (d.1+d.2+1)) : ℤ := ⌊(t.val : ℝ)/(m : ℝ)⌋
    let eta (t : Fin (d.1+d.2+1)) : ℤ := ⌊rho t/s⌋
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
    ∃ N : ℕ, ∃ cuts : Fin (N+2) → Fin (d.1+d.2+1),
      (cuts 0 = 0 ∧ cuts (Fin.last (N+1)) = Fin.last (d.1+d.2) ∧
      Monotone cuts ∧ N ≤ d.1+d.2 ∧
      (∀ i : Fin N,
        let k := cuts ⟨i.val, by omega⟩
        let l := cuts ⟨i.val+1, by omega⟩
        k < l ∧ (2*m ≤ l.val-k.val ∨ s ≤ |rho l-rho k|) ∧
        ∀ t, k < t → t < l → t.val-k.val < 2*m ∧ |rho t-rho k| < s) ∧
      (∀ t, cuts ⟨N, by omega⟩ < t →
        t.val-(cuts ⟨N, by omega⟩).val < 2*m ∧ |rho t-rho (cuts ⟨N, by omega⟩)| < s) ∧
      (∀ i : Fin (N+1),
        (cuts i.succ).val-(cuts i.castSucc).val ≤ 2*m ∧
        ∀ t, cuts i.castSucc ≤ t → t ≤ cuts i.succ →
          |rho t-rho (cuts i.castSucc)| ≤ s+1) ∧
      (∀ i : Fin N, |rho (cuts ⟨i.val+1, by omega⟩)-rho (cuts ⟨i.val, by omega⟩)| < s →
        (cuts ⟨i.val+1, by omega⟩).val-(cuts ⟨i.val, by omega⟩).val = 2*m) ∧
      (⋃ i : Fin (N+1), p.vertex '' {t | cuts i.castSucc ≤ t ∧ t < cuts i.succ}) =
        (↑p.collectedSites : Set Lattice) ∧
      (∀ i j : Fin (N+1), i ≠ j → Disjoint
        (p.vertex '' {t | cuts i.castSucc ≤ t ∧ t < cuts i.succ})
        (p.vertex '' {t | cuts j.castSucc ≤ t ∧ t < cuts j.succ})) ∧
      (∀ i : Fin (N+1), ∀ t, cuts i.castSucc ≤ t → t ≤ cuts i.succ →
        (pi (cuts i.castSucc) : ℝ)*(m : ℝ) ≤ (p.vertex t).1+(p.vertex t).2 ∧
        (p.vertex t).1+(p.vertex t).2 ≤ (pi (cuts i.castSucc) : ℝ)*(m : ℝ)+3*(m : ℝ) ∧
        |rho t-(eta (cuts i.castSucc) : ℝ)*s| ≤ 4*s) ∧
      (∀ i : Fin N,
        (pi (cuts ⟨i.val+1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 0 ∨
          pi (cuts ⟨i.val+1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 1 ∨
          pi (cuts ⟨i.val+1, by omega⟩)-pi (cuts ⟨i.val, by omega⟩) = 2) ∧
        |eta (cuts ⟨i.val+1, by omega⟩)-eta (cuts ⟨i.val, by omega⟩)| ≤ 2) ∧
      pi (cuts 0) = 0 ∧ eta (cuts 0) = 0) ∧
      ∃ capacity : Fin (N+1) → ℕ,
      ∃ time : (Σ i : Fin (N+1), Fin (capacity i)) → ℕ,
      ∃ start : (Σ i : Fin (N+1), Fin (capacity i)) → Lattice,
      ∃ displacement : (Σ i : Fin (N+1), Fin (capacity i)) → ℕ × ℕ,
      ∃ paths : (j : Σ i : Fin (N+1), Fin (capacity i)) → Path (start j) (displacement j),
      (∀ j, (cuts j.1.castSucc).val ≤ time j ∧
        time j+((displacement j).1+(displacement j).2) ≤ (cuts j.1.succ).val ∧
        segment (time j) (start j) (displacement j) (paths j) ∧
        (defectWitness (pi (cuts j.1.castSucc), eta (cuts j.1.castSucc))
            (start j) (displacement j) (paths j) ∨
          crossingWitness (pi (cuts j.1.castSucc), eta (cuts j.1.castSucc))
            (start j) (displacement j) (paths j))) ∧
      (∀ j j', j ≠ j' → Disjoint (paths j).collectedSites (paths j').collectedSites) ∧
      ((N : ℝ)-1)*η*s-4*η*s*((∑ i, capacity i : ℕ) : ℝ)-
          ∑ z ∈ p.collectedSites, max (ω z-M0) 0 ≤
        G0*((d.1 : ℝ)+(d.2 : ℝ))+((dl+dr)/2)*((1-a)*(d.1 : ℝ)-a*(d.2 : ℝ))-pathWeight ω p := by
  intro rho pi eta v segment block defectWitness crossingWitness
  obtain ⟨N, cuts, hprod⟩ := p.exists_first_cuts_blocks_indices a ha ha1 m hm s hs
  have hprodK := hprod
  obtain ⟨h0, hlast, hmono, _, hfull, hrem, _, _, _, _, _, _, _, _⟩ := hprod
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hηs : 0 ≤ η*s := mul_nonneg hη.le hs0
  -- Per-stage families: Lemma 6.8 for full stages, its remainder clause for the last.
  have hstage : ∀ i : Fin (N+1), ∃ M : ℕ, ∃ time : Fin M → ℕ, ∃ start : Fin M → Lattice,
      ∃ disp : Fin M → ℕ × ℕ, ∃ paths : (j : Fin M) → Path (start j) (disp j),
      (∀ j, (cuts i.castSucc).val ≤ time j ∧ time j+((disp j).1+(disp j).2) ≤ (cuts i.succ).val ∧
        segment (time j) (start j) (disp j) (paths j) ∧
        (defectWitness (pi (cuts i.castSucc), eta (cuts i.castSucc)) (start j) (disp j) (paths j) ∨
          crossingWitness (pi (cuts i.castSucc), eta (cuts i.castSucc)) (start j) (disp j)
            (paths j))) ∧
      (∀ j j', j ≠ j' → Disjoint (paths j).collectedSites (paths j').collectedSites) ∧
      ∀ (u : Lattice) (e : ℕ × ℕ) (y : Path u e), segment (cuts i.castSucc).val u e y →
        (cuts i.castSucc).val+(e.1+e.2) = (cuts i.succ).val →
        (i.val < N → η*s-4*η*s*(M : ℝ)-∑ z ∈ y.collectedSites, max (ω z-M0) 0 ≤
          G0*((e.1 : ℝ)+(e.2 : ℝ))+((dl+dr)/2)*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y) ∧
        -(η*s)-4*η*s*(M : ℝ)-∑ z ∈ y.collectedSites, max (ω z-M0) 0 ≤
          G0*((e.1 : ℝ)+(e.2 : ℝ))+((dl+dr)/2)*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y := by
    intro i
    have hi' := i.isLt
    by_cases hi : i.val < N
    · obtain ⟨hkl, hcut, hmin⟩ := hfull ⟨i.val, hi⟩
      obtain ⟨M, time, start, disp, paths, hmem, hdisj, hb⟩ :=
        p.full_stage_defect ω a ha ha1 m hm s hs η G0 dl dr K M0 hη hc hstep hK
          (cuts i.castSucc) (cuts i.succ) hkl hcut hmin
      exact ⟨M, time, start, disp, paths, hmem, hdisj, fun u e y hy hyl =>
        ⟨fun _ => hb u e y hy hyl, by have := hb u e y hy hyl; linarith⟩⟩
    · obtain rfl : i = Fin.last N := Fin.ext (by rw [Fin.val_last]; omega)
      obtain ⟨M, time, start, disp, paths, hmem, hdisj, hb⟩ :=
        p.stage_defect_four_witnesses ω a ha ha1 m hm s hs η G0 dl dr M0 hη hstep
          (cuts (Fin.last N).castSucc) (cuts (Fin.last N).succ)
          (hmono Fin.castSucc_lt_succ.le) (fun t h1 _ => hrem t h1)
      exact ⟨M, time, start, disp, paths, fun j => ⟨(hmem j).1, (hmem j).2.1, (hmem j).2.2.1,
        Or.inl (hmem j).2.2.2⟩, hdisj, fun u e y hy hyl =>
          ⟨fun h => (lt_irrefl N h).elim, hb u e y hy hyl⟩⟩
  choose M time start disp paths hfam using hstage
  obtain ⟨capN, hcapN⟩ : ∃ f : ℕ → ℕ, ∀ i (h : i < N+1), f i = M ⟨i, h⟩ :=
    ⟨fun i => if h : i < N+1 then M ⟨i, h⟩ else 0, fun i h => dite_eq_left h⟩
  have hp : segment 0 0 d p :=
    And.intro (by omega) (fun i t ht => congrArg p.vertex (Fin.ext (by omega)))
  obtain ⟨z0, hz0⟩ : ∃ z0 : Fin (d.1+d.2+1), z0.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  -- Summation over the stages, by induction on the number of full stages.
  have hQ : ∀ n, n ≤ N → ∀ (hn : n < N+2) (u : Lattice) (e : ℕ × ℕ) (y : Path u e),
      segment 0 u e y → 0+(e.1+e.2) = (cuts ⟨n, hn⟩).val →
      (n : ℝ)*η*s-4*η*s*((∑ i ∈ Finset.range n, capN i : ℕ) : ℝ)-
          ∑ z ∈ y.collectedSites, max (ω z-M0) 0 ≤
        G0*((e.1 : ℝ)+(e.2 : ℝ))+((dl+dr)/2)*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y := by
    intro n
    induction n with
    | zero =>
      intro _ hn u e y _ hyl
      have hc0 : (cuts ⟨0, hn⟩).val = 0 := by
        have h : (⟨0, hn⟩ : Fin (N+2)) = 0 := Fin.ext (by simp)
        rw [h, h0]
        simp
      have he1 : e.1 = 0 := by omega
      have he2 : e.2 = 0 := by omega
      have hcs : y.collectedSites = ∅ :=
        Finset.card_eq_zero.mp (by rw [Path.collectedSites_card]; omega)
      have hW : pathWeight ω y = 0 := by
        rw [Path.pathWeight_eq_sum_collectedSites, hcs, Finset.sum_empty]
      rw [hW, hcs, Finset.sum_empty, he1, he2]
      simp
    | succ n ih =>
      intro hn1 hn2 u e y hy hyl
      have hnN2 : n < N+2 := by omega
      have hnN1 : n < N+1 := by omega
      obtain ⟨en, yn, hyn, hln⟩ := p.exists_segment z0 (cuts ⟨n, hnN2⟩)
        (by rw [Fin.le_iff_val_le_val, hz0]; exact Nat.zero_le _)
      rw [hz0] at hyn hln
      obtain ⟨eS, yS, hyS, hlS⟩ := p.exists_segment (cuts ⟨n, hnN2⟩) (cuts ⟨n+1, hn2⟩)
        (hmono (Fin.mk_le_mk.mpr (Nat.le_succ n)))
      have hadd := p.segment_defect_add ω a G0 ((dl+dr)/2) M0 y yn yS 0 (cuts ⟨n, hnN2⟩).val
        hy hyn hyS hln (by omega)
      have hih := ih (by omega) hnN2 _ en yn hyn hln
      have hst := ((hfam ⟨n, hnN1⟩).2.2 _ eS yS hyS hlS).1 (show n < N by omega)
      rw [Finset.sum_range_succ, hcapN n hnN1]
      simp only [Nat.cast_add, Nat.cast_one]
      linarith [hadd.1, hadd.2]
  have hN2 : N < N+2 := by omega
  have hN1 : N+1 < N+2 := by omega
  have hNN1 : N < N+1 := by omega
  obtain ⟨eN, yN, hyN, hlN⟩ := p.exists_segment z0 (cuts ⟨N, hN2⟩)
    (by rw [Fin.le_iff_val_le_val, hz0]; exact Nat.zero_le _)
  rw [hz0] at hyN hlN
  have hlastv : (cuts ⟨N+1, hN1⟩).val = d.1+d.2 := by
    rw [show (⟨N+1, hN1⟩ : Fin (N+2)) = Fin.last (N+1) from rfl, hlast, Fin.val_last]
  obtain ⟨eS, yS, hyS, hlS⟩ := p.exists_segment (cuts ⟨N, hN2⟩) (cuts ⟨N+1, hN1⟩)
    (hmono (Fin.mk_le_mk.mpr (Nat.le_succ N)))
  have hadd := p.segment_defect_add ω a G0 ((dl+dr)/2) M0 p yN yS 0 (cuts ⟨N, hN2⟩).val
    hp hyN hyS hlN (by omega)
  have hih := hQ N le_rfl hN2 _ eN yN hyN hlN
  have hst := ((hfam ⟨N, hNN1⟩).2.2 _ eS yS hyS hlS).2
  have hsumM : (∑ i, M i) = (∑ i ∈ Finset.range N, capN i) + M ⟨N, hNN1⟩ := by
    rw [← hcapN N hNN1, ← Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range capN (N+1)]
    exact Finset.sum_congr rfl (fun i _ => (hcapN i.val i.isLt).symm)
  refine ⟨N, cuts, hprodK, M, fun j => time j.1 j.2, fun j => start j.1 j.2,
    fun j => disp j.1 j.2, fun j => paths j.1 j.2, fun j => (hfam j.1).1 j.2, ?_, ?_⟩
  · intro j j' hjj'
    obtain ⟨i, x⟩ := j
    obtain ⟨i', x'⟩ := j'
    by_cases hii : i = i'
    · subst hii
      exact (hfam i).2.1 x x' (fun h => hjj' (congrArg (Sigma.mk i) h))
    · have hm1 := (hfam i).1 x
      have hm2 := (hfam i').1 x'
      have hs1 := hm1.2.2.1
      have hs2 := hm2.2.2.1
      have hw1 := hm1.1
      have hw2 := hm1.2.1
      have hw3 := hm2.1
      have hw4 := hm2.2.1
      rcases lt_or_gt_of_ne hii with h | h
      · have h' : i.val < i'.val := h
        have hcc : (cuts i.succ).val ≤ (cuts i'.castSucc).val :=
          hmono (Fin.le_iff_val_le_val.mpr (by rw [Fin.val_succ, Fin.val_castSucc]; omega))
        exact p.segment_collectedSites_disjoint (paths i x) (paths i' x') (time i x) (time i' x')
          hs1 hs2 (by omega)
      · have h' : i'.val < i.val := h
        have hcc : (cuts i'.succ).val ≤ (cuts i.castSucc).val :=
          hmono (Fin.le_iff_val_le_val.mpr (by rw [Fin.val_succ, Fin.val_castSucc]; omega))
        exact (p.segment_collectedSites_disjoint (paths i' x') (paths i x) (time i' x')
          (time i x) hs2 hs1 (by omega)).symm
  · rw [hsumM]
    simp only [Nat.cast_add]
    linarith [hadd.1, hadd.2]

end LPPDifferentiability
