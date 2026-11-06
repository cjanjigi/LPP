/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.HeavyAttachmentNetGeometry
import Mathlib.Tactic

/-! The source region and its straight-segment tubes. -/
public section
namespace LPPDifferentiability
open scoped Classical

/-- Transverse deviation equals the first-coordinate deviation at the same
signed level; the direction parameter cancels exactly. -/
theorem heavy_attachment_deviation_identity
    (a : ℝ) (I : ℤ) (u z : Lattice) (d : ℕ × ℕ) (m : ℕ)
    (hu : u.1+u.2=I) (hd : d.1+d.2=m) (hm : 0 < m) :
    (1-a)*(z.1:ℝ)-a*(z.2:ℝ) -
      ((1-a)*(u.1:ℝ)-a*(u.2:ℝ) +
        ((z.1+z.2-I:ℤ):ℝ)*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ)) =
      (z.1:ℝ)-(u.1:ℝ)-((z.1+z.2-(u.1+u.2):ℤ):ℝ)*
        ((d.1:ℝ)/(d.1+d.2:ℕ)) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hdR : (d.1:ℝ)+(d.2:ℝ)=(m:ℝ) := by exact_mod_cast hd
  have huR : (u.1:ℝ)+(u.2:ℝ)=(I:ℝ) := by exact_mod_cast hu
  rw [hu, hd]
  push_cast
  field_simp [hm0]
  linear_combination a * ((z.1:ℝ)+(z.2:ℝ)-(I:ℝ)) * hdR +
    a * (m:ℝ) * huR

/-- Every ordered attachment rectangle satisfies the bounds for Q. -/
theorem heavy_attachment_rectangle_bounds
    (a lo hi : ℝ) (I : ℤ) (m K : ℕ) (u z : Lattice) (d : ℕ × ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hu : u.1+u.2=I)
    (hulo : lo ≤ (1-a)*(u.1:ℝ)-a*(u.2:ℝ))
    (huhi : (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ≤ hi)
    (hd : d.1+d.2=m)
    (hz : z ∈ Set.Icc u (u+((d.1:ℤ),(d.2:ℤ)))) :
    I ≤ z.1+z.2 ∧ z.1+z.2 ≤ I+(m:ℤ) ∧
      lo-(m:ℝ)-(K:ℝ)-2 ≤ (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ∧
      (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ≤ hi+(m:ℝ)+(K:ℝ)+2 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  simp only [Prod.fst_add, Prod.snd_add] at h3 h4
  have hdm : (d.1:ℤ)+(d.2:ℤ)=(m:ℤ) := by exact_mod_cast hd
  have h1r : (u.1:ℝ) ≤ (z.1:ℝ) := by exact_mod_cast h1
  have h2r : (u.2:ℝ) ≤ (z.2:ℝ) := by exact_mod_cast h2
  have h3r : (z.1:ℝ) ≤ (u.1:ℝ)+(d.1:ℝ) := by exact_mod_cast h3
  have h4r : (z.2:ℝ) ≤ (u.2:ℝ)+(d.2:ℝ) := by exact_mod_cast h4
  have hdR : (d.1:ℝ)+(d.2:ℝ)=(m:ℝ) := by exact_mod_cast hd
  have hlow := mul_le_mul_of_nonneg_left (show (z.2:ℝ)-(u.2:ℝ) ≤ (m:ℝ) by
    linarith [(Nat.cast_nonneg d.1 : (0:ℝ) ≤ d.1)]) ha.le
  have hupp := mul_le_mul_of_nonneg_left (show (z.1:ℝ)-(u.1:ℝ) ≤ (m:ℝ) by
    linarith [(Nat.cast_nonneg d.2 : (0:ℝ) ≤ d.2)]) (show 0 ≤ 1-a by linarith)
  have hn1 := mul_nonneg (show 0 ≤ 1-a by linarith) (sub_nonneg.mpr h1r)
  have hn2 := mul_nonneg ha.le (sub_nonneg.mpr h2r)
  have ham := mul_le_mul_of_nonneg_right ha1.le (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have ham0 := mul_nonneg ha.le (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  refine ⟨by omega, by omega, ?_, ?_⟩ <;> nlinarith [(Nat.cast_nonneg K : (0:ℝ) ≤ K)]

/-- Construct Q from the region construction. It contains every relevant rectangle,
and its filtered straight tubes have the count of the source. -/
theorem exists_heavy_attachment_tube_geometry
    (a D s kappa lo hi : ℝ) (I : ℤ) (K : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hD : 1 ≤ D) (hs : 4 ≤ s)
    (hkappa : 0 < kappa) (hkappaCap : kappa ≤ (1/16:ℝ))
    (hlohi : lo ≤ hi) (hwidth : hi-lo ≤ D*s)
    (hcut : 2*(K:ℝ)+5 ≤ (Nat.ceil (kappa*s):ℝ)) :
    let m := Nat.ceil (kappa*s)
    let rho := fun z : Lattice => (1-a)*(z.1:ℝ)-a*(z.2:ℝ)
    ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔ I ≤ z.1+z.2 ∧ z.1+z.2 ≤ I+(m:ℤ) ∧
        lo-(m:ℝ)-(K:ℝ)-2 ≤ rho z ∧ rho z ≤ hi+(m:ℝ)+(K:ℝ)+2) ∧
      (Q.card:ℝ) ≤ 4*D*s^2 ∧
      (∀ (u : Lattice) (d : ℕ × ℕ), u.1+u.2=I → rho u ∈ Set.Icc lo hi →
        d.1+d.2=m → ∀ z ∈ Set.Icc u (u+((d.1:ℤ),(d.2:ℤ))), z ∈ Q) ∧
      (∀ (u : Lattice) (d : ℕ × ℕ),
        ((Q.filter (fun z => |rho z-(rho u+
          ((z.1+z.2-I:ℤ):ℝ)*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))| ≤
            (K:ℝ)+2)).card:ℝ) ≤ (2*(K:ℝ)+5)*((m+1:ℕ):ℝ)) := by
  intro m rho
  obtain ⟨Q, hQ, hcard⟩ := exists_finset_heavy_attachment_region a D s kappa lo hi I K
    hD hs hkappa hkappaCap hlohi hwidth hcut
  refine ⟨Q, hQ, hcard, ?_, ?_⟩
  · intro u d hu huint hd z hz
    apply (hQ z).2
    exact heavy_attachment_rectangle_bounds a lo hi I m K u z d
      ha ha1 hu huint.1 huint.2 hd hz
  · intro u d
    let r : ℤ → ℝ := fun i => rho u+
      ((i-I:ℤ):ℝ)*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ)
    obtain ⟨S, hS, hScard⟩ := exists_finset_signed_level_nat_tube a r I m K
    have hsub : Q.filter (fun z => |rho z-r (z.1+z.2)| ≤ (K:ℝ)+2) ⊆ S := by
      intro z hz
      obtain ⟨hzQ, hzt⟩ := Finset.mem_filter.mp hz
      exact (hS z).2 ⟨((hQ z).1 hzQ).1, ((hQ z).1 hzQ).2.1, hzt⟩
    have hcount : ((Q.filter (fun z => |rho z-r (z.1+z.2)| ≤ (K:ℝ)+2)).card:ℝ) ≤
        (S.card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    exact hcount.trans (by nlinarith only [hScard])

/-- Rectangle-filtered greedy tubes of the source lie in the same Sigma. -/
theorem heavy_attachment_greedy_tube_subset
    (a : ℝ) (I : ℤ) (m K : ℕ) (Q : Finset Lattice) (u : Lattice) (d : ℕ × ℕ)
    (hu : u.1+u.2=I) (hd : d.1+d.2=m) (hm : 0 < m)
    (hrect : ∀ z ∈ Set.Icc u (u+((d.1:ℤ),(d.2:ℤ))), z ∈ Q) :
    (Finset.Icc u (u+((d.1:ℤ),(d.2:ℤ)))).filter (fun z =>
      |(z.1:ℝ)-(u.1:ℝ)-((z.1+z.2-(u.1+u.2):ℤ):ℝ)*
        ((d.1:ℝ)/(d.1+d.2:ℕ))| ≤ (K:ℝ)+2) ⊆
    Q.filter (fun z => |(1-a)*(z.1:ℝ)-a*(z.2:ℝ)-
      ((1-a)*(u.1:ℝ)-a*(u.2:ℝ)+((z.1+z.2-I:ℤ):ℝ)*
        ((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))| ≤ (K:ℝ)+2) := by
  intro z hz
  obtain ⟨hzrect, hzdev⟩ := Finset.mem_filter.mp hz
  apply Finset.mem_filter.mpr
  refine ⟨hrect z (Finset.mem_Icc.mp hzrect), ?_⟩
  rw [heavy_attachment_deviation_identity a I u z d m hu hd hm]
  exact hzdev

end LPPDifferentiability
