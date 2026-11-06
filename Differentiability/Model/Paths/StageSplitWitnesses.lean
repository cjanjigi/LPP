/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Split
public import Differentiability.Model.Paths.StageGeometry
public import LPP_Foundations.Model.Animals.PathSets
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-! Segments of an actual path and the greedy split of a stage into disjoint defect witnesses
(Lemma B.8 of the differentiability preprint). -/

public section

open scoped BigOperators

namespace LPPDifferentiability

/-- The vertex of a path at a natural local time, zero past the end. -/
private def vtx {d : ℕ × ℕ} (p : Path 0 d) (t : ℕ) : Lattice :=
  if h : t < d.1+d.2+1 then p.vertex ⟨t, h⟩ else 0

private theorem vtx_fin {d : ℕ × ℕ} (p : Path 0 d) (t : Fin (d.1+d.2+1)) :
    vtx p t.val = p.vertex t := by
  unfold vtx
  exact dite_eq_left t.isLt

private theorem vtx_inj {d : ℕ × ℕ} (p : Path 0 d) {t t' : ℕ} (ht : t < d.1+d.2+1)
    (ht' : t' < d.1+d.2+1) (h : vtx p t = vtx p t') : t = t' := by
  have h1 := vtx_fin p ⟨t, ht⟩
  have h2 := vtx_fin p ⟨t', ht'⟩
  have h3 : p.vertex ⟨t, ht⟩ = p.vertex ⟨t', ht'⟩ := h1.symm.trans (h.trans h2)
  exact congrArg Fin.val (p.vertex_injective h3)

/-- The collected sites of a segment are the path's vertices at the segment's
terminal-excluded window of local times. -/
private theorem seg_cs {d : ℕ × ℕ} (p : Path 0 d) {u : Lattice} {e : ℕ × ℕ}
    (y : Path u e) (k0 : ℕ)
    (hy : k0+(e.1+e.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)),
      t.val = k0+i.val → y.vertex i = p.vertex t) :
    y.collectedSites = (Finset.Ico k0 (k0+(e.1+e.2))).image (vtx p) := by
  obtain ⟨hfit, hv⟩ := hy
  ext z
  rw [Path.mem_collectedSites_iff, Finset.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    refine ⟨k0+i.val, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [hv i.castSucc ⟨k0+i.val, by omega⟩ rfl]
    exact vtx_fin p ⟨k0+i.val, by omega⟩
  · rintro ⟨t, ht, rfl⟩
    rw [Finset.mem_Ico] at ht
    have hlt : t < d.1+d.2+1 := by omega
    refine ⟨⟨t-k0, by omega⟩, ?_⟩
    rw [hv (Fin.castSucc ⟨t-k0, by omega⟩) ⟨t, hlt⟩ (show t = k0+(t-k0) by omega)]
    exact (vtx_fin p ⟨t, hlt⟩).symm

private theorem seg_sum {d : ℕ × ℕ} (p : Path 0 d) {u : Lattice} {e : ℕ × ℕ}
    (y : Path u e) (k0 : ℕ)
    (hy : k0+(e.1+e.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)),
      t.val = k0+i.val → y.vertex i = p.vertex t) (f : Lattice → ℝ) :
    ∑ z ∈ y.collectedSites, f z = ∑ t ∈ Finset.Ico k0 (k0+(e.1+e.2)), f (vtx p t) := by
  have hfit := hy.1
  rw [seg_cs p y k0 hy, Finset.sum_image]
  intro t ht t' ht' h
  simp only [Finset.coe_Ico, Set.mem_Ico] at ht ht'
  obtain ⟨_, ht2⟩ := ht
  obtain ⟨_, ht2'⟩ := ht'
  exact vtx_inj p (by omega) (by omega) h

/-- The literal support defect of a segment in terms of the path's vertices. -/
private theorem seg_defect {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment) (a G sl : ℝ)
    {u : Lattice} {e : ℕ × ℕ} (y : Path u e) (k0 : ℕ)
    (hy : k0+(e.1+e.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)),
      t.val = k0+i.val → y.vertex i = p.vertex t) :
    G*((e.1 : ℝ)+(e.2 : ℝ))+sl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y =
      G*(((k0+(e.1+e.2) : ℕ) : ℝ)-(k0 : ℝ)) +
        sl*(((1-a)*((vtx p (k0+(e.1+e.2))).1 : ℝ)-a*((vtx p (k0+(e.1+e.2))).2 : ℝ)) -
          ((1-a)*((vtx p k0).1 : ℝ)-a*((vtx p k0).2 : ℝ))) -
        ∑ t ∈ Finset.Ico k0 (k0+(e.1+e.2)), ω (vtx p t) := by
  have hsum := seg_sum p y k0 hy ω
  obtain ⟨hfit, hv⟩ := hy
  have h0 : y.vertex 0 = vtx p k0 := by
    rw [hv 0 ⟨k0, by omega⟩ (by simp)]
    exact (vtx_fin p ⟨k0, by omega⟩).symm
  have hl : y.vertex (Fin.last (e.1+e.2)) = vtx p (k0+(e.1+e.2)) := by
    rw [hv (Fin.last (e.1+e.2)) ⟨k0+(e.1+e.2), by omega⟩ (by simp)]
    exact (vtx_fin p ⟨k0+(e.1+e.2), by omega⟩).symm
  have hdisp : vtx p (k0+(e.1+e.2)) = vtx p k0 + ((e.1 : ℤ), (e.2 : ℤ)) := by
    rw [← hl, y.finish, ← h0, y.start]
  have hx : ((vtx p (k0+(e.1+e.2))).1 : ℝ) = ((vtx p k0).1 : ℝ)+(e.1 : ℝ) := by
    rw [hdisp]
    simp only [Prod.fst_add, Int.cast_add, Int.cast_natCast]
  have hy2 : ((vtx p (k0+(e.1+e.2))).2 : ℝ) = ((vtx p k0).2 : ℝ)+(e.2 : ℝ) := by
    rw [hdisp]
    simp only [Prod.snd_add, Int.cast_add, Int.cast_natCast]
  rw [Path.pathWeight_eq_sum_collectedSites, hsum, hx, hy2]
  push_cast
  ring

/-- The segment of an actual path between two local times exists: it is the
prefix of the suffix. -/
theorem Path.exists_segment {d : ℕ × ℕ} (p : Path 0 d) (k l : Fin (d.1+d.2+1)) (hkl : k ≤ l) :
    ∃ e : ℕ × ℕ, ∃ y : Path (p.vertex k) e,
      (k.val+(e.1+e.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)),
        t.val = k.val+i.val → y.vertex i = p.vertex t) ∧ k.val+(e.1+e.2) = l.val := by
  have hkl' : k.val ≤ l.val := hkl
  have hl := l.isLt
  have hsuf := p.suffix_length k
  obtain ⟨j, hj⟩ : ∃ j : Fin ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2 + 1),
      j.val = l.val - k.val := ⟨⟨l.val - k.val, by omega⟩, rfl⟩
  have hlen := (p.suffix k).splitDisplacement_length j
  refine ⟨(p.suffix k).splitDisplacement j, (p.suffix k).prefixPath j, ⟨by omega, ?_⟩, by omega⟩
  intro i
  have hi := i.isLt
  have hb : k.val + i.val < d.1+d.2+1 := by omega
  intro t ht
  have htk : t = ⟨k.val + i.val, hb⟩ := Fin.ext ht
  subst htk
  rfl

/-- Every vertex of a segment is a vertex of the path at the shifted local time. -/
theorem Path.segment_vertex {d : ℕ × ℕ} (p : Path 0 d) {u : Lattice} {e : ℕ × ℕ}
    (y : Path u e) (k0 : ℕ)
    (hy : k0+(e.1+e.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)),
      t.val = k0+i.val → y.vertex i = p.vertex t) (i : Fin (e.1+e.2+1)) :
    ∃ t : Fin (d.1+d.2+1), t.val = k0+i.val ∧ y.vertex i = p.vertex t := by
  have hi := i.isLt
  have hfit := hy.1
  exact ⟨⟨k0+i.val, by omega⟩, rfl, hy.2 i ⟨k0+i.val, by omega⟩ rfl⟩

/-- A segment starts at the path's vertex at its first time, and its displacement is
the difference of the path's vertices at its two end times. -/
theorem Path.segment_endpoints {d : ℕ × ℕ} (p : Path 0 d) {u : Lattice} {e : ℕ × ℕ}
    (y : Path u e) (k0 : ℕ)
    (hy : k0+(e.1+e.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)),
      t.val = k0+i.val → y.vertex i = p.vertex t)
    (t₀ t₁ : Fin (d.1+d.2+1)) (h₀ : t₀.val = k0) (h₁ : t₁.val = k0+(e.1+e.2)) :
    u = p.vertex t₀ ∧ (e.1 : ℤ) = (p.vertex t₁).1-(p.vertex t₀).1 ∧
      (e.2 : ℤ) = (p.vertex t₁).2-(p.vertex t₀).2 := by
  obtain ⟨_, hv⟩ := hy
  have h0 : y.vertex 0 = p.vertex t₀ := hv 0 t₀ (by simp [h₀])
  have hl : y.vertex (Fin.last (e.1+e.2)) = p.vertex t₁ := hv (Fin.last (e.1+e.2)) t₁ (by simp [h₁])
  have hs := y.start
  have hf := y.finish
  rw [h0] at hs
  rw [hl, ← hs] at hf
  refine ⟨hs.symm, ?_, ?_⟩
  · have h := congrArg Prod.fst hf
    simp only [Prod.fst_add] at h
    omega
  · have h := congrArg Prod.snd hf
    simp only [Prod.snd_add] at h
    omega

/-- Two consecutive segments: every support defect and the total excess add up. -/
theorem Path.segment_defect_add {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment) (a G sl M0 : ℝ)
    {u u₁ u₂ : Lattice} {e e₁ e₂ : ℕ × ℕ} (y : Path u e) (y₁ : Path u₁ e₁) (y₂ : Path u₂ e₂)
    (k₀ k₁ : ℕ)
    (hy : k₀+(e.1+e.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)),
      t.val = k₀+i.val → y.vertex i = p.vertex t)
    (hy₁ : k₀+(e₁.1+e₁.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e₁.1+e₁.2+1)) (t : Fin (d.1+d.2+1)),
      t.val = k₀+i.val → y₁.vertex i = p.vertex t)
    (hy₂ : k₁+(e₂.1+e₂.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e₂.1+e₂.2+1)) (t : Fin (d.1+d.2+1)),
      t.val = k₁+i.val → y₂.vertex i = p.vertex t)
    (hk₁ : k₀+(e₁.1+e₁.2) = k₁) (hlen : k₀+(e.1+e.2) = k₁+(e₂.1+e₂.2)) :
    G*((e.1 : ℝ)+(e.2 : ℝ))+sl*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y =
      (G*((e₁.1 : ℝ)+(e₁.2 : ℝ))+sl*((1-a)*(e₁.1 : ℝ)-a*(e₁.2 : ℝ))-pathWeight ω y₁) +
        (G*((e₂.1 : ℝ)+(e₂.2 : ℝ))+sl*((1-a)*(e₂.1 : ℝ)-a*(e₂.2 : ℝ))-pathWeight ω y₂) ∧
    ∑ z ∈ y.collectedSites, max (ω z-M0) 0 =
      ∑ z ∈ y₁.collectedSites, max (ω z-M0) 0 + ∑ z ∈ y₂.collectedSites, max (ω z-M0) 0 := by
  have hk : k₀ ≤ k₁ := by omega
  have hk' : k₁ ≤ k₁+(e₂.1+e₂.2) := Nat.le_add_right _ _
  constructor
  · rw [seg_defect p ω a G sl y k₀ hy, seg_defect p ω a G sl y₁ k₀ hy₁,
      seg_defect p ω a G sl y₂ k₁ hy₂, hlen, hk₁, ← Finset.sum_Ico_consecutive _ hk hk']
    ring
  · rw [seg_sum p y k₀ hy (fun z => max (ω z-M0) 0), seg_sum p y₁ k₀ hy₁ (fun z => max (ω z-M0) 0),
      seg_sum p y₂ k₁ hy₂ (fun z => max (ω z-M0) 0), hlen, hk₁,
      ← Finset.sum_Ico_consecutive _ hk hk']

/-- Segments with disjoint terminal-excluded windows have disjoint collected sites. -/
theorem Path.segment_collectedSites_disjoint {d : ℕ × ℕ} (p : Path 0 d)
    {u₁ u₂ : Lattice} {e₁ e₂ : ℕ × ℕ} (y₁ : Path u₁ e₁) (y₂ : Path u₂ e₂) (k₁ k₂ : ℕ)
    (hy₁ : k₁+(e₁.1+e₁.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e₁.1+e₁.2+1)) (t : Fin (d.1+d.2+1)),
      t.val = k₁+i.val → y₁.vertex i = p.vertex t)
    (hy₂ : k₂+(e₂.1+e₂.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e₂.1+e₂.2+1)) (t : Fin (d.1+d.2+1)),
      t.val = k₂+i.val → y₂.vertex i = p.vertex t)
    (h : k₁+(e₁.1+e₁.2) ≤ k₂) :
    Disjoint y₁.collectedSites y₂.collectedSites := by
  have hf₁ := hy₁.1
  have hf₂ := hy₂.1
  rw [seg_cs p y₁ k₁ hy₁, seg_cs p y₂ k₂ hy₂, Finset.disjoint_left]
  intro z hz1 hz2
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz1
  obtain ⟨t', ht', htt⟩ := Finset.mem_image.mp hz2
  rw [Finset.mem_Ico] at ht ht'
  have := vtx_inj p (t := t') (t' := t) (by omega) (by omega) htt
  omega

/-- The greedy split of Lemma 6.5 of the differentiability preprint, for abstract additive
defects and excesses on an interval of natural times. -/
private theorem greedy_split (c : ℝ) (hc : 0 ≤ c) (D Z : ℕ → ℕ → ℝ) (L : ℕ)
    (hadd : ∀ i j l, i ≤ j → j ≤ l → D i l = D i j + D j l)
    (hZadd : ∀ i j l, i ≤ j → j ≤ l → Z i l = Z i j + Z j l)
    (hZ : ∀ i j, 0 ≤ Z i j) (hzero : ∀ i, D i i = 0)
    (hone : ∀ i, i+1 ≤ L → -(c/2) - Z i (i+1) ≤ D i (i+1)) :
    ∀ r i, L - i = r → i ≤ L → ∃ F : Finset (ℕ × ℕ),
      (∀ w ∈ F, i ≤ w.1 ∧ w.1 < w.2 ∧ w.2 ≤ L ∧ D w.1 w.2 < -c) ∧
      (∀ w ∈ F, ∀ w' ∈ F, w ≠ w' → w.2 ≤ w'.1 ∨ w'.2 ≤ w.1) ∧
      -c - 2*c*(F.card : ℝ) - Z i L ≤ D i L := by
  classical
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro i hr hiL
    by_cases hex : ∃ j, i < j ∧ j ≤ L ∧ D i j < -c
    · obtain ⟨j, ⟨hij, hjL, hDj⟩, hmin⟩ : ∃ j, (i < j ∧ j ≤ L ∧ D i j < -c) ∧
          ∀ j', j' < j → ¬ (i < j' ∧ j' ≤ L ∧ D i j' < -c) :=
        ⟨Nat.find hex, Nat.find_spec hex, fun j' h => Nat.find_min hex h⟩
      have hprev : -c ≤ D i (j-1) := by
        by_cases h : i < j-1
        · by_contra hneg
          exact hmin (j-1) (by omega) ⟨h, by omega, not_le.mp hneg⟩
        · have hj1 : j-1 = i := by omega
          rw [hj1, hzero]
          linarith
      have hlast := hone (j-1) (by omega)
      have hj1 : j-1+1 = j := by omega
      rw [hj1] at hlast
      have hsplit := hadd i (j-1) j (by omega) (by omega)
      have hZsplit := hZadd i (j-1) j (by omega) (by omega)
      have hZnn := hZ i (j-1)
      obtain ⟨F, hF, hFdisj, hFb⟩ := ih (L-j) (by omega) j rfl hjL
      have hnot : (i, j) ∉ F := by
        intro hmem
        have h' : j ≤ i := (hF _ hmem).1
        omega
      refine ⟨insert (i, j) F, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact ⟨le_refl i, hij, hjL, hDj⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hF w hw
          exact ⟨by omega, h2, h3, h4⟩
      · intro w hw w' hw' hne
        rcases Finset.mem_insert.mp hw with rfl | hw <;>
          rcases Finset.mem_insert.mp hw' with rfl | hw'
        · exact absurd rfl hne
        · exact Or.inl (hF w' hw').1
        · exact Or.inr (hF w hw).1
        · exact hFdisj w hw w' hw' hne
      · rw [Finset.card_insert_of_notMem hnot, hadd i j L (by omega) hjL,
          hZadd i j L (by omega) hjL]
        push_cast
        linarith
    · refine ⟨∅, by simp, by simp, ?_⟩
      have hD : -c ≤ D i L := by
        rcases Nat.eq_or_lt_of_le hiL with h | h
        · rw [h, hzero]
          linarith
        · by_contra hneg
          exact hex ⟨L, h, le_refl L, not_le.mp hneg⟩
      rw [Finset.card_empty, Nat.cast_zero]
      linarith [hZ i L]

/-- The greedy split of a stage (Lemma 6.5 of the differentiability preprint, and its general
form, Lemma B.8): disjoint ordered windows in `[k,l]` whose segments have average defect below
`-ηs`, and a bound for the defect of the stage by `-ηs - 2ηs` per window minus the total excess
of the stage's collected sites. -/
theorem Path.stage_greedy_windows {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (s η G0 dl dr M0 : ℝ) (hc0 : 0 ≤ η*s)
    (hstep : |G0| + |(dl+dr)/2| + M0 ≤ η*s/2) (k l : Fin (d.1+d.2+1)) (hkl : k ≤ l) :
    ∃ F : Finset (ℕ × ℕ),
      (∀ w ∈ F, k.val ≤ w.1 ∧ w.1 < w.2 ∧ w.2 ≤ l.val ∧
        ∀ (u : Lattice) (e : ℕ × ℕ) (y : Path u e),
          (w.1+(e.1+e.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)),
            t.val = w.1+i.val → y.vertex i = p.vertex t) → w.1+(e.1+e.2) = w.2 →
          G0*((e.1 : ℝ)+(e.2 : ℝ))+((dl+dr)/2)*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y <
            -(η*s)) ∧
      (∀ w ∈ F, ∀ w' ∈ F, w ≠ w' → w.2 ≤ w'.1 ∨ w'.2 ≤ w.1) ∧
      ∀ (u : Lattice) (e : ℕ × ℕ) (y : Path u e),
        (k.val+(e.1+e.2) ≤ d.1+d.2 ∧ ∀ (i : Fin (e.1+e.2+1)) (t : Fin (d.1+d.2+1)),
          t.val = k.val+i.val → y.vertex i = p.vertex t) → k.val+(e.1+e.2) = l.val →
        -(η*s)-2*η*s*(F.card : ℝ)-∑ z ∈ y.collectedSites, max (ω z-M0) 0 ≤
          G0*((e.1 : ℝ)+(e.2 : ℝ))+((dl+dr)/2)*((1-a)*(e.1 : ℝ)-a*(e.2 : ℝ))-pathWeight ω y := by
  have hkl' : k.val ≤ l.val := hkl
  have hlt := l.isLt
  let R : ℕ → ℝ := fun t => (1-a)*((vtx p t).1 : ℝ)-a*((vtx p t).2 : ℝ)
  let D : ℕ → ℕ → ℝ := fun i j =>
    G0*((j : ℝ)-(i : ℝ))+((dl+dr)/2)*(R j-R i)-∑ t ∈ Finset.Ico i j, ω (vtx p t)
  let Z : ℕ → ℕ → ℝ := fun i j => ∑ t ∈ Finset.Ico i j, max (ω (vtx p t)-M0) 0
  have hadd : ∀ i j l', i ≤ j → j ≤ l' → D i l' = D i j + D j l' := by
    intro i j l' h1 h2
    simp only [D]
    rw [← Finset.sum_Ico_consecutive _ h1 h2]
    ring
  have hZadd : ∀ i j l', i ≤ j → j ≤ l' → Z i l' = Z i j + Z j l' := by
    intro i j l' h1 h2
    simp only [Z]
    exact (Finset.sum_Ico_consecutive _ h1 h2).symm
  have hZ : ∀ i j, 0 ≤ Z i j := by
    intro i j
    simp only [Z]
    exact Finset.sum_nonneg (fun t _ => le_max_right _ _)
  have hzero : ∀ i, D i i = 0 := by
    intro i
    simp only [D, Finset.Ico_self, Finset.sum_empty]
    ring
  have hsum1 : ∀ (i : ℕ) (f : ℕ → ℝ), ∑ t ∈ Finset.Ico i (i+1), f t = f i := by
    intro i f
    rw [Finset.sum_Ico_succ_top (le_refl i), Finset.Ico_self, Finset.sum_empty, zero_add]
  have hone : ∀ i, i+1 ≤ l.val → -(η*s/2) - Z i (i+1) ≤ D i (i+1) := by
    intro i hi
    have hiL : i < d.1+d.2 := by omega
    have hvi : vtx p i = p.vertex (⟨i, hiL⟩ : Fin (d.1+d.2)).castSucc :=
      vtx_fin p (⟨i, hiL⟩ : Fin (d.1+d.2)).castSucc
    have hvi1 : vtx p (i+1) = p.vertex (⟨i, hiL⟩ : Fin (d.1+d.2)).succ :=
      vtx_fin p (⟨i, hiL⟩ : Fin (d.1+d.2)).succ
    have hstepR : |R (i+1)-R i| ≤ 1 := by
      simp only [R]
      rw [hvi, hvi1]
      exact transverse_step p a ha ha1 ⟨i, hiL⟩
    have hZ1 : Z i (i+1) = max (ω (vtx p i)-M0) 0 := by
      simp only [Z]
      exact hsum1 i (fun t => max (ω (vtx p t)-M0) 0)
    have hD1 : D i (i+1) = G0*(((i+1 : ℕ) : ℝ)-(i : ℝ))+((dl+dr)/2)*(R (i+1)-R i)-ω (vtx p i) := by
      simp only [D]
      rw [hsum1 i (fun t => ω (vtx p t))]
    rw [hZ1, hD1]
    have hcast : (((i+1 : ℕ) : ℝ)-(i : ℝ)) = 1 := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [hcast]
    have h2 : |(dl+dr)/2*(R (i+1)-R i)| ≤ |(dl+dr)/2| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hstepR
    have h3 := neg_abs_le ((dl+dr)/2*(R (i+1)-R i))
    have h4 : ω (vtx p i)-M0 ≤ max (ω (vtx p i)-M0) 0 := le_max_left _ _
    have h5 := neg_abs_le G0
    linarith
  obtain ⟨F, hF, hFdisj, hFb⟩ :=
    greedy_split (η*s) hc0 D Z l.val hadd hZadd hZ hzero hone (l.val-k.val) k.val rfl hkl'
  refine ⟨F, fun w hw => ?_, hFdisj, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hF w hw
    refine ⟨h1, h2, h3, fun u e y hy hyl => ?_⟩
    have hdef := seg_defect p ω a G0 ((dl+dr)/2) y w.1 hy
    rw [hyl] at hdef
    have h4' := h4
    simp only [D, R] at h4'
    linarith
  · intro u e y hy hyl
    have hdef := seg_defect p ω a G0 ((dl+dr)/2) y k.val hy
    have hexc := seg_sum p y k.val hy (fun z => max (ω z-M0) 0)
    rw [hyl] at hdef hexc
    have hFb' := hFb
    simp only [D, Z, R] at hFb'
    linarith

end LPPDifferentiability
