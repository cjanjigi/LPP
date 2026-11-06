/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.StageGeometry
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-! Closed blocks and consecutive indices for the actual first cuts. -/

public section

namespace LPPDifferentiability

/-- Floor-window inequality: `⌊x/b⌋ b ≤ x < (⌊x/b⌋ + 1) b` for `b > 0`. -/
theorem floor_window (x b : ℝ) (hb : 0 < b) :
    (⌊x/b⌋ : ℝ)*b ≤ x ∧ x < ((⌊x/b⌋ : ℝ)+1)*b := by
  exact ⟨(le_div_iff₀ hb).mp (Int.floor_le (x/b)),
    (div_lt_iff₀ hb).mp (Int.lt_floor_add_one (x/b))⟩

private theorem floor_step (x y b D : ℝ) (hb : 0 < b) (hD : D ≤ 2*b)
    (hxy : x ≤ y) (hyx : y-x ≤ D) :
    ⌊y/b⌋-⌊x/b⌋ = 0 ∨ ⌊y/b⌋-⌊x/b⌋ = 1 ∨ ⌊y/b⌋-⌊x/b⌋ = 2 := by
  have hx := floor_window x b hb
  have hy := floor_window y b hb
  have hlo : ⌊x/b⌋ ≤ ⌊y/b⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right hxy hb.le)
  have hup : (⌊y/b⌋ : ℝ) < (⌊x/b⌋ : ℝ)+3 := by nlinarith
  have hup' : ⌊y/b⌋ < ⌊x/b⌋+3 := by exact_mod_cast hup
  omega

private theorem transverse_floor_step (x y s : ℝ) (hs : 2 ≤ s)
    (hxy : |y-x| ≤ s+1) : |⌊y/s⌋-⌊x/s⌋| ≤ 2 := by
  have hpos : 0 < s := by linarith
  have hx := floor_window x s hpos
  have hy := floor_window y s hpos
  have h := abs_le.mp hxy
  have hup : (⌊y/s⌋ : ℝ)-(⌊x/s⌋ : ℝ) < 3 := by nlinarith
  have hlo : -3 < (⌊y/s⌋ : ℝ)-(⌊x/s⌋ : ℝ) := by nlinarith
  have hup' : ⌊y/s⌋-⌊x/s⌋ < 3 := by exact_mod_cast hup
  have hlo' : -3 < ⌊y/s⌋-⌊x/s⌋ := by exact_mod_cast hlo
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- First cuts, closed blocks, collected slices, and consecutive indices
with all witnesses and constants shared. -/
theorem Path.exists_first_cuts_blocks_indices {d : ℕ × ℕ} (p : Path 0 d)
    (a : ℝ) (ha : 0<a) (ha1 : a<1) (m : ℕ) (hm : 1≤m) (s : ℝ) (hs : 2≤s) :
    let rho (t : Fin (d.1+d.2+1)) : ℝ := (1-a)*(p.vertex t).1-a*(p.vertex t).2
    let pi (t : Fin (d.1+d.2+1)) : ℤ := ⌊(t.val : ℝ)/(m : ℝ)⌋
    let eta (t : Fin (d.1+d.2+1)) : ℤ := ⌊rho t/s⌋
    ∃ N : ℕ, ∃ cuts : Fin (N+2) → Fin (d.1+d.2+1),
      cuts 0 = 0 ∧ cuts (Fin.last (N+1)) = Fin.last (d.1+d.2) ∧
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
      pi (cuts 0) = 0 ∧ eta (cuts 0) = 0 := by
  dsimp only
  obtain ⟨N, cuts, h0, hlast, hmono, hN, hfull, hrem, hgeometry, hlong, hunion, hdisj⟩ :=
    p.exists_geometric_first_cuts a ha ha1 m hm s hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsR : 0 < s := by linarith
  refine ⟨N, cuts, h0, hlast, hmono, hN, hfull, hrem, hgeometry, hlong, hunion, hdisj, ?_, ?_, ?_, ?_⟩
  · intro i t hkt htl
    let k := cuts i.castSucc
    let l := cuts i.succ
    have hkl : k.val ≤ l.val := hmono (by change i.val ≤ i.val+1; omega)
    have hd := (Nat.cast_le (α := ℝ)).mpr (hgeometry i).1
    rw [Nat.cast_sub hkl, Nat.cast_mul, Nat.cast_ofNat] at hd
    have hktR : (k.val : ℝ) ≤ t.val := by exact_mod_cast hkt
    have htlR : (t.val : ℝ) ≤ l.val := by exact_mod_cast htl
    have hlev := p.level t
    simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at hlev
    have hlevR : ((p.vertex t).1 : ℝ)+((p.vertex t).2 : ℝ) = t.val := by exact_mod_cast hlev
    have hkfloor := floor_window (k.val : ℝ) m hmR
    have hrfloor := floor_window ((1-a)*(p.vertex k).1-a*(p.vertex k).2) s hsR
    have htbound := abs_le.mp ((hgeometry i).2 t hkt htl)
    refine ⟨?_, ?_, ?_⟩
    · change (⌊(k.val : ℝ)/(m : ℝ)⌋ : ℝ)*(m : ℝ) ≤ _
      linarith
    · change _ ≤ (⌊(k.val : ℝ)/(m : ℝ)⌋ : ℝ)*(m : ℝ)+3*(m : ℝ)
      nlinarith
    · apply abs_le.mpr
      change -(4*s) ≤ _ ∧ _ ≤ 4*s
      constructor <;> linarith
  · intro i
    let k := cuts ⟨i.val, by omega⟩
    let l := cuts ⟨i.val+1, by omega⟩
    have hkl : k.val ≤ l.val := (hfull i).1.le
    have hd := (Nat.cast_le (α := ℝ)).mpr (hgeometry ⟨i.val, by omega⟩).1
    simp only [Fin.succ_mk, Fin.castSucc_mk] at hd
    rw [Nat.cast_sub hkl, Nat.cast_mul, Nat.cast_ofNat] at hd
    constructor
    · exact floor_step k.val l.val m (2*(m : ℝ)) hmR le_rfl (by exact_mod_cast hkl) hd
    · exact transverse_floor_step _ _ s hs
        ((hgeometry ⟨i.val, by omega⟩).2 l (by exact (hfull i).1.le) le_rfl)
  · rw [h0]
    simp only [Fin.val_zero, Nat.cast_zero, zero_div, Int.floor_zero]
  · rw [h0, p.start]
    simp only [Prod.fst_zero, Prod.snd_zero, Int.cast_zero, mul_zero, sub_self, zero_div,
      Int.floor_zero]

end LPPDifferentiability
