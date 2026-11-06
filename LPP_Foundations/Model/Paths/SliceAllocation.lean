/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Axes
public import LPP_Foundations.Model.Paths.HorizontalFirst
public import LPP_Foundations.Model.Paths.Split
import LPP_Foundations.Model.Paths.Count
import Mathlib.Algebra.BigOperators.Fin

/-! Finite planar allocations into vertical slices and horizontal joining steps.
All passage values and paths omit the terminal vertex. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Heights of the `a` horizontal steps of a path of displacement `(a,b)`. -/
def SliceAllocation (a b : ℕ) := {h : Fin a → Fin (b + 1) // Monotone h}

namespace SliceAllocation

/-- The implicit initial height is zero and the implicit final height is `b`. -/
def height {a b : ℕ} (h : SliceAllocation a b) (i : Fin (a + 2)) : ℕ :=
  if hi : i.val = 0 then 0
  else if hj : i.val < a + 1 then (h.val ⟨i.val - 1, by omega⟩).val
  else b

@[simp] theorem height_zero {a b : ℕ} (h : SliceAllocation a b) : h.height 0 = 0 := by
  simp only [height, Fin.val_zero, ↓reduceDIte]

@[simp] theorem height_last {a b : ℕ} (h : SliceAllocation a b) :
    h.height (Fin.last (a + 1)) = b := by
  simp [height]

/-- Each horizontal step occurs at its literal prescribed height. -/
theorem height_join {a b : ℕ} (h : SliceAllocation a b) (i : Fin a) :
    h.height i.succ.castSucc = (h.val i).val := by
  simp only [height, Fin.val_castSucc, Fin.val_succ]
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 2

theorem height_monotone {a b : ℕ} (h : SliceAllocation a b) : Monotone h.height := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  unfold height
  split_ifs with hi hj hk hl
  all_goals try omega
  exact h.property (by change i.val - 1 ≤ j.val - 1; omega)

/-- Vertical passage values plus weights at the horizontal joining sites. -/
noncomputable def weight {a b : ℕ} (h : SliceAllocation a b)
    (ω : Environment) (u : Lattice) : ℝ :=
  (∑ r : Fin (a + 1), lastPassage ω
    (u.1 + (r.val : ℤ), u.2 + (h.height r.castSucc : ℤ))
    (0, h.height r.succ - h.height r.castSucc)) +
  ∑ r : Fin a, ω (u.1 + (r.val : ℤ), u.2 + (h.val r).val)

end SliceAllocation

/-- A monotone sequence with initial height zero is realized by actual vertical
slices and horizontal joins. The single path works for every environment. -/
theorem exists_path_vertical_slices_and_joins (a : ℕ) (m : Fin (a + 2) → ℕ)
    (hm : Monotone m) (hzero : m 0 = 0) (u : Lattice) :
    ∃ p : Path u (a, m (Fin.last (a + 1))),
      (∀ r : Fin a, ∃ i : Fin (a + m (Fin.last (a + 1))),
        p.vertex i.castSucc = (u.1 + (r.val : ℤ), u.2 + (m r.succ.castSucc : ℤ)) ∧
        p.vertex i.succ = p.vertex i.castSucc + (1, 0)) ∧
      ∀ ω : Environment,
      pathWeight ω p =
        (∑ r : Fin (a + 1), lastPassage ω
          (u.1 + (r.val : ℤ), u.2 + (m r.castSucc : ℤ))
          (0, m r.succ - m r.castSucc)) +
        ∑ r : Fin a, ω (u.1 + (r.val : ℤ), u.2 + (m r.succ.castSucc : ℤ)) := by
  have hcast_vertex {d e : ℕ × ℕ} (he : d = e) (t : Path u d)
      (i : Fin (e.1 + e.2 + 1)) :
      (he ▸ t).vertex i = t.vertex ⟨i.val, by
        have hh := congrArg (fun v : ℕ × ℕ => v.1 + v.2 + 1) he
        have hi := i.isLt
        omega⟩ := by
    subst e
    rfl
  induction a with
  | zero =>
    refine ⟨horizontalFirst u (0, m (Fin.last 1)), ?_, ?_⟩
    · intro r
      exact Fin.elim0 r
    · intro ω
      rw [pathWeight_vertical, Fin.sum_univ_one, Fin.sum_univ_zero, add_zero]
      change (∑ i : Fin (m (Fin.last 1)), ω (u.1, u.2 + (i.val : ℤ))) =
        lastPassage ω (u.1 + 0, u.2 + (m 0 : ℤ)) (0, m (Fin.last 1) - m 0)
      rw [hzero]
      simp only [Nat.cast_zero, add_zero, Nat.sub_zero]
      exact (lastPassage_vertical ω u (m (Fin.last 1))).symm
  | succ a ih =>
    let m' : Fin (a + 2) → ℕ := fun i => m i.castSucc
    have hm' : Monotone m' := fun i j hij => hm (Fin.castSucc_le_castSucc_iff.mpr hij)
    have hz' : m' 0 = 0 := hzero
    obtain ⟨p, hpj, hp⟩ := ih m' hm' hz' hcast_vertex
    let c := m (Fin.last (a + 1)).castSucc
    let b := m (Fin.last (a + 2))
    have hcb : c ≤ b := hm (Fin.le_last _)
    let v : Lattice := u + ((a : ℤ), (c : ℤ))
    let q := horizontalFirst v (1, 0)
    let w : Lattice := u + (((((a, c) : ℕ × ℕ) + (1, 0)).1 : ℤ),
      (((((a, c) : ℕ × ℕ) + (1, 0)).2 : ℤ)))
    let z := horizontalFirst w (0, b - c)
    have hpType : m' (Fin.last (a + 1)) = c := rfl
    let pq := p.concat q
    let pz := pq.concat z
    have hd : ((a, m' (Fin.last (a + 1))) + (1, 0) + (0, b - c) : ℕ × ℕ) =
        (a + 1, b) := by
      apply Prod.ext
      · change a + 1 + 0 = a + 1
        omega
      · change m' (Fin.last (a + 1)) + 0 + (b - c) = b
        rw [hpType]
        omega
    refine ⟨hd ▸ pz, ?_, ?_⟩
    · have hleft (j : Fin (a + c + 1)) :
          (hd ▸ pz).vertex ⟨j.val, by
            have hj := j.isLt
            omega⟩ = p.vertex j := by
        rw [hcast_vertex]
        exact (pq.concat_vertex_left z ⟨j.val, by
          have hj := j.isLt
          change j.val < (a + 1) + (c + 0) + 1
          omega⟩).trans (p.concat_vertex_left q j)
      have hmid (j : Fin (1 + 0 + 1)) :
          (hd ▸ pz).vertex ⟨a + c + j.val, by
            have hj := j.isLt
            omega⟩ = q.vertex j := by
        rw [hcast_vertex]
        exact (pq.concat_vertex_left z ⟨a + c + j.val, by
          have hj := j.isLt
          change a + c + j.val < (a + 1) + (c + 0) + 1
          omega⟩).trans (p.concat_vertex_right q j)
      intro r
      refine Fin.lastCases ?_ (fun r => ?_) r
      · refine ⟨⟨a + c, by change a + c < a + 1 + b; omega⟩, ?_, ?_⟩
        · exact (hmid 0).trans q.start
        · calc
            (hd ▸ pz).vertex (⟨a + c, by omega⟩ : Fin (a + 1 + b)).succ =
                q.vertex (Fin.last 1) := hmid (Fin.last 1)
            _ = q.vertex 0 + (1, 0) := q.finish.trans
              (congrArg (fun t : Lattice => t + (1, 0)) q.start.symm)
            _ = (hd ▸ pz).vertex (⟨a + c, by omega⟩ : Fin (a + 1 + b)).castSucc +
                (1, 0) := congrArg (fun t : Lattice => t + (1, 0)) (hmid 0).symm
      · obtain ⟨i, hiv, hie⟩ := hpj r
        refine ⟨⟨i.val, by
          change i.val < a + 1 + b
          have hi : i.val < a + c := i.isLt
          omega⟩, ?_, ?_⟩
        · exact (hleft i.castSucc).trans hiv
        · exact (hleft i.succ).trans (hie.trans
            (congrArg (fun t : Lattice => t + (1, 0)) (hleft i.castSucc).symm))
    · intro ω
      have hw : pathWeight ω (hd ▸ pz) = pathWeight ω p +
          pathWeight ω q + pathWeight ω z := by
        have hcast {d e : ℕ × ℕ} (he : d = e) (t : Path u d) :
            pathWeight ω (he ▸ t) = pathWeight ω t := by
          subst e
          rfl
        rw [hcast, pathWeight_concat, pathWeight_concat]
      rw [hw, hp, pathWeight_horizontal, pathWeight_vertical,
        Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, add_zero]
      conv_rhs =>
        lhs
        rw [Fin.sum_univ_castSucc]
      conv_rhs =>
        rhs
        rw [Fin.sum_univ_castSucc]
      have hslice : lastPassage ω
          (u.1 + ((Fin.last (a + 1)).val : ℤ),
            u.2 + (m (Fin.last (a + 1)).castSucc : ℤ))
          (0, m (Fin.last (a + 1)).succ - m (Fin.last (a + 1)).castSucc) =
          ∑ i : Fin (b - c), ω (w.1, w.2 + (i.val : ℤ)) := by
        exact lastPassage_vertical ω _ _
      rw [hslice]
      have heq : (∑ r : Fin (a + 1), lastPassage ω
          (u.1 + (r.val : ℤ), u.2 + (m' r.castSucc : ℤ))
          (0, m' r.succ - m' r.castSucc)) =
          ∑ r : Fin (a + 1), lastPassage ω
            (u.1 + (r.castSucc.val : ℤ), u.2 + (m r.castSucc.castSucc : ℤ))
            (0, m r.castSucc.succ - m r.castSucc.castSucc) := by
        rfl
      rw [heq]
      have hjoin : ω (v.1, v.2) = ω
          (u.1 + ((Fin.last a).val : ℤ), u.2 + (m (Fin.last a).succ.castSucc : ℤ)) := by
        rfl
      rw [hjoin]
      ac_rfl

/-- A monotone sequence with initial height zero is realized by actual vertical
slices and horizontal joins. The single path works for every environment. -/
theorem exists_path_vertical_slices (a : ℕ) (m : Fin (a + 2) → ℕ)
    (hm : Monotone m) (hzero : m 0 = 0) (u : Lattice) :
    ∃ p : Path u (a, m (Fin.last (a + 1))), ∀ ω : Environment,
      pathWeight ω p =
        (∑ r : Fin (a + 1), lastPassage ω
          (u.1 + (r.val : ℤ), u.2 + (m r.castSucc : ℤ))
          (0, m r.succ - m r.castSucc)) +
        ∑ r : Fin a, ω (u.1 + (r.val : ℤ), u.2 + (m r.succ.castSucc : ℤ)) := by
  obtain ⟨p, _, hp⟩ := exists_path_vertical_slices_and_joins a m hm hzero u
  exact ⟨p, hp⟩

/-- Every literal allocation is realized by one actual path for all weights. -/
theorem SliceAllocation.exists_path {a b : ℕ} (h : SliceAllocation a b) (u : Lattice) :
    ∃ p : Path u (a, b), ∀ ω : Environment, pathWeight ω p = h.weight ω u := by
  obtain ⟨p, hp⟩ :=
    exists_path_vertical_slices a h.height h.height_monotone h.height_zero u
  have he : (a, h.height (Fin.last (a + 1))) = (a, b) :=
    congrArg (fun n : ℕ => (a, n)) h.height_last
  refine ⟨he ▸ p, ?_⟩
  intro ω
  have hcast {d e : ℕ × ℕ} (he' : d = e) (t : Path u d) :
      pathWeight ω (he' ▸ t) = pathWeight ω t := by
    subst e
    rfl
  rw [hcast, hp]
  simp only [SliceAllocation.weight, SliceAllocation.height_join]

/-- Every allocation's exact slice expression is bounded by actual last passage. -/
theorem SliceAllocation.weight_le_lastPassage {a b : ℕ} (h : SliceAllocation a b)
    (ω : Environment) (u : Lattice) : h.weight ω u ≤ lastPassage ω u (a, b) := by
  obtain ⟨p, hp⟩ := h.exists_path u
  rw [← hp ω]
  exact pathWeight_le_lastPassage ω p

/-- Slice lengths telescope to the vertical displacement, also for repeated heights. -/
theorem SliceAllocation.sum_slice_lengths {a b : ℕ} (h : SliceAllocation a b) :
    ∑ r : Fin (a + 1), (h.height r.succ - h.height r.castSucc) = b := by
  have he : (∑ r : Fin (a + 1), (h.height r.succ - h.height r.castSucc)) +
      (∑ r : Fin (a + 1), h.height r.castSucc) =
      ∑ r : Fin (a + 1), h.height r.succ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    exact Nat.sub_add_cancel (h.height_monotone (Fin.castSucc_le_succ r))
  have hs := Fin.sum_univ_succ h.height
  have ht := Fin.sum_univ_castSucc h.height
  rw [h.height_zero, zero_add] at hs
  rw [h.height_last] at ht
  omega

/-- Horizontal joining sites are distinct, regardless of repeated heights. -/
theorem SliceAllocation.join_sites_injective {a b : ℕ} (h : SliceAllocation a b)
    (u : Lattice) :
    Function.Injective (fun r : Fin a =>
      (u.1 + (r.val : ℤ), u.2 + ((h.val r).val : ℤ))) := by
  intro i j hij
  have hx := congrArg Prod.fst hij
  apply Fin.ext
  change u.1 + (i.val : ℤ) = u.1 + (j.val : ℤ) at hx
  omega

/-- At every column before the terminal column, an actual path has exactly one
horizontal step leaving that column. -/
theorem Path.exists_unique_east_at_column {a b : ℕ} {u : Lattice}
    (p : Path u (a, b)) (r : Fin a) :
    ∃! i : Fin (a + b),
      (p.vertex i.castSucc).1 = u.1 + (r.val : ℤ) ∧
      p.vertex i.succ = p.vertex i.castSucc + (1, 0) := by
  classical
  let s : Finset (Fin (a + b + 1)) :=
    Finset.univ.filter (fun i => (p.vertex i).1 ≤ u.1 + (r.val : ℤ))
  have h0 : (0 : Fin (a + b + 1)) ∈ s := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [p.start]
    omega
  have hs : s.Nonempty := ⟨0, h0⟩
  let k := s.max' hs
  have hk : (p.vertex k).1 ≤ u.1 + (r.val : ℤ) :=
    (Finset.mem_filter.mp (s.max'_mem hs)).2
  have hklt : k.val < a + b := by
    have hi := k.isLt
    by_contra hn
    have he : k = Fin.last (a + b) := Fin.ext (by
      simp only [Fin.val_last]
      omega)
    rw [he, p.finish] at hk
    change u.1 + (a : ℤ) ≤ u.1 + (r.val : ℤ) at hk
    have hr := r.isLt
    omega
  let i : Fin (a + b) := ⟨k.val, hklt⟩
  have hnext : u.1 + (r.val : ℤ) < (p.vertex i.succ).1 := by
    by_contra hn
    have his : i.succ ∈ s :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hle := Finset.le_max' s i.succ his
    change i.val + 1 ≤ k.val at hle
    dsimp only [i] at hle
    omega
  have heast : p.vertex i.succ = p.vertex i.castSucc + (1, 0) := by
    rcases p.step i with he | hn
    · exact he
    · rw [hn] at hnext
      change u.1 + (r.val : ℤ) < (p.vertex i.castSucc).1 + 0 at hnext
      change (p.vertex i.castSucc).1 ≤ u.1 + (r.val : ℤ) at hk
      omega
  have hx : (p.vertex i.castSucc).1 = u.1 + (r.val : ℤ) := by
    have hv := congrArg Prod.fst heast
    change (p.vertex i.succ).1 = (p.vertex i.castSucc).1 + 1 at hv
    change (p.vertex i.castSucc).1 ≤ u.1 + (r.val : ℤ) at hk
    omega
  refine ⟨i, ⟨hx, heast⟩, ?_⟩
  intro j hj
  by_cases hji : j.val < i.val
  · have hh := p.fst_monotone (show j.succ ≤ i.castSucc from by
      change j.val + 1 ≤ i.val
      omega)
    dsimp only at hh
    rw [hj.2] at hh
    change (p.vertex j.castSucc).1 + 1 ≤ (p.vertex i.castSucc).1 at hh
    rw [hj.1, hx] at hh
    omega
  · by_cases hij : i.val < j.val
    · have hh := p.fst_monotone (show i.succ ≤ j.castSucc from by
        change i.val + 1 ≤ j.val
        omega)
      dsimp only at hh
      rw [heast] at hh
      change (p.vertex i.castSucc).1 + 1 ≤ (p.vertex j.castSucc).1 at hh
      rw [hx, hj.1] at hh
      omega
    · exact Fin.ext (by omega)

/-- The path's horizontal joining vertices have exactly the allocation heights. -/
def SliceAllocation.realizes {a b : ℕ} {u : Lattice} (h : SliceAllocation a b)
    (p : Path u (a, b)) : Prop :=
  ∀ r : Fin a, ∃ i : Fin (a + b),
    p.vertex i.castSucc = (u.1 + (r.val : ℤ), u.2 + ((h.val r).val : ℤ)) ∧
    p.vertex i.succ = p.vertex i.castSucc + (1, 0)

/-- Reading the horizontal steps of an actual path recovers a unique allocation. -/
theorem Path.exists_unique_sliceAllocation {a b : ℕ} {u : Lattice}
    (p : Path u (a, b)) : ∃! h : SliceAllocation a b, h.realizes p := by
  classical
  have hex (r : Fin a) := p.exists_unique_east_at_column r
  choose idx hidx using fun r : Fin a => (hex r).exists
  let f : Fin a → Fin (b + 1) := fun r =>
    ⟨(p.splitDisplacement (idx r).castSucc).2, by
      have hb := (p.splitDisplacement_le (idx r).castSucc).2
      omega⟩
  have hcast (r : Fin a) : ((f r).val : ℤ) =
      (p.vertex (idx r).castSucc).2 - u.2 :=
    p.splitDisplacement_snd_cast (idx r).castSucc
  have hf : Monotone f := by
    intro r s hrs
    have hi : idx r ≤ idx s := by
      by_contra hn
      have hsr : (idx s).val < (idx r).val := by
        change ¬ (idx r).val ≤ (idx s).val at hn
        omega
      have hh := p.fst_monotone (show (idx s).succ ≤ (idx r).castSucc from by
        change (idx s).val + 1 ≤ (idx r).val
        omega)
      dsimp only at hh
      rw [(hidx s).2] at hh
      change (p.vertex (idx s).castSucc).1 + 1 ≤ (p.vertex (idx r).castSucc).1 at hh
      rw [(hidx s).1, (hidx r).1] at hh
      have hrs' : r.val ≤ s.val := hrs
      omega
    have hh := p.snd_monotone (Fin.castSucc_le_castSucc_iff.mpr hi)
    dsimp only at hh
    have hr := hcast r
    have hs := hcast s
    change (f r).val ≤ (f s).val
    omega
  let h : SliceAllocation a b := ⟨f, hf⟩
  have hreal : h.realizes p := by
    intro r
    refine ⟨idx r, ?_, (hidx r).2⟩
    apply Prod.ext
    · exact (hidx r).1
    · have hc := hcast r
      change (p.vertex (idx r).castSucc).2 = u.2 + ((f r).val : ℤ)
      omega
  refine ⟨h, hreal, ?_⟩
  intro h' hh'
  apply Subtype.ext
  funext r
  apply Fin.ext
  obtain ⟨j, hjv, hje⟩ := hh' r
  have hjx : (p.vertex j.castSucc).1 = u.1 + (r.val : ℤ) :=
    congrArg Prod.fst hjv
  have hji : j = idx r := (hex r).unique ⟨hjx, hje⟩ (hidx r)
  have hy := congrArg Prod.snd hjv
  rw [hji] at hy
  have hc := hcast r
  change ((h'.val r).val : ℕ) = (f r).val
  change (p.vertex (idx r).castSucc).2 = u.2 + ((h'.val r).val : ℤ) at hy
  omega

/-- Construct an actual path with the stated joining vertices and exact weight. -/
theorem SliceAllocation.exists_path_realizing {a b : ℕ} (h : SliceAllocation a b)
    (u : Lattice) :
    ∃ p : Path u (a, b), h.realizes p ∧
      ∀ ω : Environment, pathWeight ω p = h.weight ω u := by
  let P (n : ℕ) : Prop := ∃ p : Path u (a, n),
    (∀ r : Fin a, ∃ i : Fin (a + n),
      p.vertex i.castSucc = (u.1 + (r.val : ℤ), u.2 + ((h.val r).val : ℤ)) ∧
      p.vertex i.succ = p.vertex i.castSucc + (1, 0)) ∧
    ∀ ω : Environment, pathWeight ω p = h.weight ω u
  have he : P (h.height (Fin.last (a + 1))) := by
    simpa only [P, SliceAllocation.height_join, SliceAllocation.weight] using
      exists_path_vertical_slices_and_joins a h.height h.height_monotone h.height_zero u
  have hb : P b := Eq.mp (congrArg P h.height_last) he
  exact hb

/-- The horizontal joining vertices determine the actual path uniquely. -/
theorem Path.eq_of_realizes {a b : ℕ} {u : Lattice} {h : SliceAllocation a b}
    {p q : Path u (a, b)} (hp : h.realizes p) (hq : h.realizes q) : p = q := by
  classical
  have transfer (p q : Path u (a, b)) (hp : h.realizes p) (hq : h.realizes q)
      (i : Fin (a + b))
      (he : p.vertex i.succ = p.vertex i.castSucc + (1, 0)) :
      q.vertex i.succ = q.vertex i.castSucc + (1, 0) := by
    let c := (p.splitDisplacement i.castSucc).1
    have hc : c < a := by
      have hb := (p.vertex_mem_Icc i.succ).2.1
      have hf := p.splitDisplacement_fst_cast i.castSucc
      rw [he] at hb
      simp only [Prod.fst_add] at hb
      dsimp only [c]
      omega
    let r : Fin a := ⟨c, hc⟩
    have hx : (p.vertex i.castSucc).1 = u.1 + (r.val : ℤ) := by
      have hf := p.splitDisplacement_fst_cast i.castSucc
      change (p.vertex i.castSucc).1 = u.1 + (c : ℤ)
      omega
    obtain ⟨j, hjv, hje⟩ := hp r
    have hjx : (p.vertex j.castSucc).1 = u.1 + (r.val : ℤ) :=
      congrArg Prod.fst hjv
    have hji : j = i := (p.exists_unique_east_at_column r).unique ⟨hjx, hje⟩ ⟨hx, he⟩
    have hiv : p.vertex i.castSucc =
        (u.1 + (r.val : ℤ), u.2 + ((h.val r).val : ℤ)) := hji ▸ hjv
    obtain ⟨k, hkv, hke⟩ := hq r
    have hlp := p.level i.castSucc
    have hlq := q.level k.castSucc
    rw [hiv] at hlp
    rw [hkv] at hlq
    simp only [Fin.val_castSucc] at hlp hlq
    have hki : k = i := Fin.ext (by omega)
    exact hki ▸ hke
  apply stepCode_injective u (a, b)
  funext i
  by_cases he : p.vertex i.succ = p.vertex i.castSucc + (1, 0)
  · have hf := transfer p q hp hq i he
    simp only [stepCode, he, hf, decide_true]
  · have hf : ¬ q.vertex i.succ = q.vertex i.castSucc + (1, 0) :=
      fun hh => he (transfer q p hq hp i hh)
    simp only [stepCode, he, hf, decide_false]

/-- A literal allocation has precisely one actual realizing path. -/
theorem SliceAllocation.exists_unique_path {a b : ℕ} (h : SliceAllocation a b)
    (u : Lattice) : ∃! p : Path u (a, b), h.realizes p := by
  obtain ⟨p, hp, _⟩ := h.exists_path_realizing u
  exact ⟨p, hp, fun q hq => Path.eq_of_realizes hq hp⟩

/-- Every actual realizing path has the exact slice and join weight. -/
theorem SliceAllocation.pathWeight_eq {a b : ℕ} {u : Lattice}
    (h : SliceAllocation a b) (p : Path u (a, b)) (hp : h.realizes p) (ω : Environment) :
    pathWeight ω p = h.weight ω u := by
  obtain ⟨q, hq, hw⟩ := h.exists_path_realizing u
  rw [Path.eq_of_realizes hp hq]
  exact hw ω

/-- Every actual path recovers its unique allocation and exact weight identity. -/
theorem Path.exists_unique_sliceAllocation_weight {a b : ℕ} {u : Lattice}
    (p : Path u (a, b)) :
    ∃! h : SliceAllocation a b, h.realizes p ∧
      ∀ ω : Environment, pathWeight ω p = h.weight ω u := by
  obtain ⟨h, hh, hu⟩ := p.exists_unique_sliceAllocation
  refine ⟨h, ⟨hh, fun ω => h.pathWeight_eq p hh ω⟩, ?_⟩
  intro h' hh'
  exact hu h' hh'.1

noncomputable instance SliceAllocation.fintype (a b : ℕ) : Fintype (SliceAllocation a b) := by
  classical
  unfold SliceAllocation
  infer_instance

instance SliceAllocation.nonempty (a b : ℕ) : Nonempty (SliceAllocation a b) :=
  ⟨⟨fun _ => 0, fun _ _ _ => le_rfl⟩⟩

/-- Actual paths and literal allocations have the same finite cardinality. -/
theorem sliceAllocation_card_eq_path_card (u : Lattice) (a b : ℕ) :
    Fintype.card (SliceAllocation a b) = Fintype.card (Path u (a, b)) := by
  classical
  let f : SliceAllocation a b → Path u (a, b) :=
    fun h => Classical.choose (h.exists_unique_path u).exists
  have hf (h : SliceAllocation a b) : h.realizes (f h) :=
    Classical.choose_spec (h.exists_unique_path u).exists
  have hinj : Function.Injective f := by
    intro h k he
    obtain ⟨z, _, hu⟩ := (f h).exists_unique_sliceAllocation
    have hh : h.realizes (f h) := hf h
    have hk : k.realizes (f h) := by rw [he]; exact hf k
    exact (hu h hh).trans (hu k hk).symm
  have hsurj : Function.Surjective f := by
    intro p
    obtain ⟨h, hh, _⟩ := p.exists_unique_sliceAllocation
    exact ⟨h, Path.eq_of_realizes (hf h) hh⟩
  exact Fintype.card_of_bijective ⟨hinj, hsurj⟩

/-- The finite allocation count has the required binomial upper bound. -/
theorem sliceAllocation_card_le_choose (a b : ℕ) :
    Fintype.card (SliceAllocation a b) ≤ Nat.choose (a + b) a := by
  rw [sliceAllocation_card_eq_path_card (0 : Lattice)]
  exact path_card_le_choose 0 (a, b)

/-- Martin's finite planar maximum is over the actual allocations. -/
theorem lastPassage_eq_max_sliceAllocation (ω : Environment) (u : Lattice) (a b : ℕ) :
    lastPassage ω u (a, b) =
      (Finset.univ.image (fun h : SliceAllocation a b => h.weight ω u)).max'
        (Finset.Nonempty.image Finset.univ_nonempty _) := by
  classical
  apply le_antisymm
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u (a, b)
    obtain ⟨h, ⟨_, hw⟩, _⟩ := p.exists_unique_sliceAllocation_weight
    rw [← hp, hw ω]
    have hh : h.weight ω u ∈
        Finset.univ.image (fun k : SliceAllocation a b => k.weight ω u) :=
      Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩
    exact Finset.le_max' _ _ hh
  · obtain ⟨h, _, hh⟩ := Finset.mem_image.mp (Finset.max'_mem
      (Finset.univ.image (fun h : SliceAllocation a b => h.weight ω u))
      (Finset.Nonempty.image Finset.univ_nonempty _))
    rw [← hh]
    exact h.weight_le_lastPassage ω u

end LPPDifferentiability
