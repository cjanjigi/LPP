/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.StageCuts
import Mathlib.Tactic

/-! Geometry and actual collected slices for the same first cuts. -/

public section

namespace LPPDifferentiability

/-- One step of an up-right path changes the transverse coordinate `(1-a)x - a y` by at most 1. -/
theorem transverse_step {d : ℕ × ℕ} (p : Path 0 d) (a : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (i : Fin (d.1+d.2)) :
    |((1-a)*(p.vertex i.succ).1-a*(p.vertex i.succ).2) -
      ((1-a)*(p.vertex i.castSucc).1-a*(p.vertex i.castSucc).2)| ≤ 1 := by
  rcases p.step i with h | h <;> rw [h] <;>
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one, Int.cast_zero]
  · rw [show (1-a)*((p.vertex i.castSucc).1+1)-a*((p.vertex i.castSucc).2+0)-
        ((1-a)*(p.vertex i.castSucc).1-a*(p.vertex i.castSucc).2) = 1-a by ring]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [show (1-a)*((p.vertex i.castSucc).1+0)-a*((p.vertex i.castSucc).2+1)-
        ((1-a)*(p.vertex i.castSucc).1-a*(p.vertex i.castSucc).2) = -a by ring]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Let `k ≤ l` be indices of `p` such that every index strictly between them is less than `2m`
after `k` and has transverse deviation below `s` from `k`. Then `l - k ≤ 2m`, and every index in
`[k, l]` has transverse deviation at most `s + 1`. -/
theorem interval_geometry {d : ℕ × ℕ} (p : Path 0 d) (a : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 1 ≤ m)
    (s : ℝ) (hs : 2 ≤ s) (k l : Fin (d.1+d.2+1)) (hkl : k ≤ l)
    (hmin : ∀ t, k < t → t < l → t.val-k.val < 2*m ∧
      |((1-a)*(p.vertex t).1-a*(p.vertex t).2) -
        ((1-a)*(p.vertex k).1-a*(p.vertex k).2)| < s) :
    l.val-k.val ≤ 2*m ∧
    ∀ t, k ≤ t → t ≤ l →
      |((1-a)*(p.vertex t).1-a*(p.vertex t).2) -
        ((1-a)*(p.vertex k).1-a*(p.vertex k).2)| ≤ s+1 := by
  let rho (t : Fin (d.1+d.2+1)) : ℝ :=
    (1-a)*(p.vertex t).1-a*(p.vertex t).2
  have hbefore : ∀ t, k ≤ t → t < l →
      t.val-k.val < 2*m ∧ |rho t-rho k| < s := by
    intro t hkt htl
    rcases eq_or_lt_of_le hkt with h | h
    · subst t
      dsimp [rho]
      simp only [Nat.sub_self, sub_self, abs_zero]
      constructor <;> linarith
    · exact hmin t h htl
  by_cases heq : k = l
  · subst l
    refine ⟨by omega, ?_⟩
    intro t hkt htk
    have ht : t = k := le_antisymm htk hkt
    subst t
    simp only [sub_self, abs_zero]
    linarith
  · have hlt : k.val < l.val := by exact lt_of_le_of_ne hkl (fun h => heq (Fin.ext h))
    let j : Fin (d.1+d.2) := ⟨l.val-1, by omega⟩
    have hj : j.succ = l := Fin.ext (by dsimp [j]; omega)
    have hkj : k ≤ j.castSucc := by change k.val ≤ l.val-1; omega
    have hjl : j.castSucc < l := by change l.val-1 < l.val; omega
    obtain ⟨hdur, htrans⟩ := hbefore j.castSucc hkj hjl
    have hstep : |rho l-rho j.castSucc| ≤ 1 := by
      simpa only [rho, hj] using transverse_step p a ha ha1 j
    refine ⟨by dsimp [j] at hdur; omega, ?_⟩
    intro t hkt htl
    rcases eq_or_lt_of_le htl with ht | ht
    · subst t
      calc
        |rho l-rho k| = |(rho l-rho j.castSucc)+(rho j.castSucc-rho k)| := by ring_nf
        _ ≤ |rho l-rho j.castSucc|+|rho j.castSucc-rho k| := abs_add_le _ _
        _ ≤ s+1 := by linarith
    · exact (hbefore t hkt ht).2.le.trans (by linarith)

private theorem slice_partition {d : ℕ × ℕ} (p : Path 0 d) (N : ℕ)
    (c : Fin (N+2) → Fin (d.1+d.2+1)) (h0 : c 0 = 0)
    (hlast : c (Fin.last (N+1)) = Fin.last (d.1+d.2)) (hmono : Monotone c) :
    (⋃ i : Fin (N+1), p.vertex ''
      {t | c i.castSucc ≤ t ∧ t < c i.succ}) = (↑p.collectedSites : Set Lattice) ∧
    (∀ i j : Fin (N+1), i ≠ j → Disjoint
      (p.vertex '' {t | c i.castSucc ≤ t ∧ t < c i.succ})
      (p.vertex '' {t | c j.castSucc ≤ t ∧ t < c j.succ})) := by
  classical
  constructor
  · ext z
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨i, t, ⟨_, htl⟩, rfl⟩
      have htL := lt_of_lt_of_le htl (hmono (Fin.le_last i.succ))
      rw [hlast] at htL
      refine (p.mem_collectedSites_iff _).2 ⟨⟨t.val, htL⟩, ?_⟩
      congr 1
    · intro hz
      obtain ⟨t, rfl⟩ := (p.mem_collectedSites_iff _).1 hz
      have hex : ∃ j : ℕ, ∃ hj : j < N+2, t.castSucc < c ⟨j,hj⟩ :=
        ⟨N+1, by omega, by
          change t.castSucc < c (Fin.last (N+1))
          rw [hlast]
          exact t.isLt⟩
      obtain ⟨hj, htj⟩ := Nat.find_spec hex
      have hj0 : 0 < Nat.find hex := by
        by_contra hn
        have he : Nat.find hex = 0 := by omega
        have hc : (⟨Nat.find hex,hj⟩ : Fin (N+2)) = 0 := Fin.ext he
        rw [hc, h0] at htj
        exact (Fin.not_lt_zero t.castSucc) htj
      let i : Fin (N+1) := ⟨Nat.find hex-1, by omega⟩
      refine ⟨i, t.castSucc, ⟨?_, ?_⟩, rfl⟩
      · by_contra hn
        exact Nat.find_min hex (show i.val < Nat.find hex by dsimp [i]; omega)
          ⟨i.castSucc.isLt, lt_of_not_ge hn⟩
      · have hi : i.succ = (⟨Nat.find hex,hj⟩ : Fin (N+2)) :=
          Fin.ext (by dsimp [i]; omega)
        rw [hi]
        exact htj
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨t, ⟨hit, hti⟩, htz⟩ ⟨u, ⟨hju, huj⟩, huz⟩
    have htu : t = u := p.vertex_injective (htz.trans huz.symm)
    subst u
    rcases lt_or_gt_of_ne hij with h | h
    · have hc := hmono (show i.succ ≤ j.castSucc by change i.val+1 ≤ j.val; omega)
      exact (not_lt_of_ge (hc.trans hju)) hti
    · have hc := hmono (show j.succ ≤ i.castSucc by change j.val+1 ≤ i.val; omega)
      exact (not_lt_of_ge (hc.trans hit)) huj

/-- The actual least-cut partition has the geometric bounds of the differentiability preprint and a
literal terminal-excluded collected-slice partition, all for the same returned cuts. -/
theorem Path.exists_geometric_first_cuts {d : ℕ × ℕ} (p : Path 0 d)
    (a : ℝ) (ha : 0<a) (ha1 : a<1) (m : ℕ) (hm : 1≤m) (s : ℝ) (hs : 2≤s) :
    let rho (t : Fin (d.1+d.2+1)) : ℝ := latticeTransverseCoordinate a (p.vertex t)
    ∃ N : ℕ, ∃ cuts : Fin (N+2) → Fin (d.1+d.2+1),
      cuts 0 = 0 ∧ cuts (Fin.last (N+1)) = Fin.last (d.1+d.2) ∧
      Monotone cuts ∧ N ≤ d.1+d.2 ∧
      (∀ i : Fin N,
        let k := cuts ⟨i.val, by omega⟩
        let l := cuts ⟨i.val+1, by omega⟩
        k < l ∧ p.reaches_stage_cut a m s k l ∧
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
        (p.vertex '' {t | cuts j.castSucc ≤ t ∧ t < cuts j.succ})) := by
  dsimp only
  obtain ⟨N, cuts, h0, hlast, hmono, hN, hfull, hrem⟩ := p.exists_first_cuts a m s
  have hgeometry : ∀ i : Fin (N+1),
      (cuts i.succ).val-(cuts i.castSucc).val ≤ 2*m ∧
      ∀ t, cuts i.castSucc ≤ t → t ≤ cuts i.succ →
        |((1-a)*(p.vertex t).1-a*(p.vertex t).2)-
          ((1-a)*(p.vertex (cuts i.castSucc)).1-a*(p.vertex (cuts i.castSucc)).2)| ≤ s+1 := by
    intro i
    apply interval_geometry p a ha ha1 m hm s hs (cuts i.castSucc) (cuts i.succ)
      (hmono (by change i.val ≤ i.val+1; omega))
    intro t hkt htl
    by_cases hi : i.val < N
    · exact (hfull ⟨i.val, hi⟩).2.2 t hkt htl
    · have hie : i.castSucc = (⟨N, by omega⟩ : Fin (N+2)) := Fin.ext (by change i.val = N; omega)
      rw [hie] at hkt ⊢
      exact hrem t hkt
  obtain ⟨hunion, hdisj⟩ := slice_partition p N cuts h0 hlast hmono
  refine ⟨N, cuts, h0, hlast, hmono, hN, hfull, hrem, hgeometry, ?_, hunion, hdisj⟩
  intro i ht
  have hg := (hgeometry ⟨i.val, by omega⟩).1
  rcases (p.reaches_stage_cut_iff a m s _ _).mp (hfull i).2.1 with hd | hr
  · exact Nat.le_antisymm hg hd
  · exact (not_le_of_gt ht hr).elim

end LPPDifferentiability
