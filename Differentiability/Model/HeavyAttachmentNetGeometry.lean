/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.MiddleNetAttachment
public import Differentiability.Model.HeavyAttachmentRegionCardinality
import Mathlib.Tactic

/-! The common forward net and starting interval for heavy attachments. -/
public section
namespace LPPDifferentiability

/-- The starting interval and one common central net, chosen before all starts.
The bounds describe this constructed net, not every net that might be supplied. -/
theorem exists_heavy_attachment_common_net
    (a D s kappa lo hi : ℝ) (I : ℤ)
    (ha : 0 < a) (ha1 : a < 1) (hD : 1 ≤ D) (hs : 4 ≤ s)
    (hkappa : 0 < kappa) (hkappaCap : kappa ≤ (1 / 16 : ℝ))
    (hlohi : lo ≤ hi) (hwidth : hi - lo ≤ D * s)
    (hspacing : 1 ≤ min a (1-a) * (Nat.ceil (kappa*s) : ℝ) / 4) :
    let m := Nat.ceil (kappa*s)
    let rho := fun z : Lattice => (1-a)*(z.1:ℝ)-a*(z.2:ℝ)
    ∃ (J : Finset Lattice) (M : ℕ) (v : Fin (M+1) → Lattice),
      (∀ u, u ∈ J ↔ u.1+u.2=I ∧ rho u ∈ Set.Icc lo hi) ∧
      (J.card : ℝ) ≤ D*s+1 ∧
      1 ≤ M ∧ Function.Injective v ∧
      (∀ j, (v j).1+(v j).2=I+(m:ℤ) ∧
        rho (v j) ∈ Set.Icc (lo-a*(m:ℝ)) (hi+(1-a)*(m:ℝ))) ∧
      (∀ (j : ℕ) (hj : j < M),
        min a (1-a)*(m:ℝ)/4 ≤
          rho (v ⟨j+1, by omega⟩)-rho (v ⟨j, by omega⟩) ∧
        rho (v ⟨j+1, by omega⟩)-rho (v ⟨j, by omega⟩) ≤
          min a (1-a)*(m:ℝ)/2) ∧
      (∀ j, (rho (v j) ≤ lo-a*(m:ℝ)+min a (1-a)*(m:ℝ)/2) ↔ j.val=0) ∧
      (∀ j, (hi+(1-a)*(m:ℝ)-min a (1-a)*(m:ℝ)/2 ≤ rho (v j)) ↔ j.val=M) ∧
      rho (v ⟨0, by omega⟩) ≤ lo-a*(m:ℝ)+min a (1-a)*(m:ℝ)/2 ∧
      hi+(1-a)*(m:ℝ)-min a (1-a)*(m:ℝ)/2 ≤ rho (v ⟨M, by omega⟩) ∧
      (M+1:ℝ) < 4*(hi-lo+(m:ℝ))/(min a (1-a)*(m:ℝ)) ∧
      (M+1:ℝ) ≤ 8*D/(min a (1-a)*kappa)+2 ∧
      (∀ u ∈ J, ∃ (j : Fin (M+1)) (d : ℕ × ℕ),
        d.1+d.2=m ∧ u+((d.1:ℤ),(d.2:ℤ))=v j ∧
        (d.1:ℝ)/(m:ℝ) ∈ Set.Icc (1/4) (3/4) ∧
        |rho (v j-u)| ≤ (m:ℝ)) := by
  classical
  intro m rho
  obtain ⟨J, hJ, hJcard⟩ := exists_finset_level_interval a lo hi I hlohi
  obtain ⟨M, v, hM, hinj, hnet, hgap, hfirstOnly, hlastOnly, hfirst, hlast,
      hcard, hattach⟩ :=
    exists_forward_middle_net_attachments a ha ha1 m hspacing I lo hi hlohi
  have ht : 0 < min a (1-a) := lt_min ha (by linarith)
  have hs0 : 0 ≤ s := by linarith
  have hmceil : (m:ℝ) ≤ kappa*s+1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hkappa.le hs0)).le
  have hmlo : kappa*s ≤ (m:ℝ) := Nat.le_ceil _
  have hmpos : 0 < (m:ℝ) := by nlinarith [hspacing]
  have hmle : (m:ℝ) ≤ s := by
    have hh := mul_le_mul_of_nonneg_right hkappaCap hs0
    nlinarith
  have hDs : s ≤ D*s := by nlinarith
  have hnum : hi-lo+(m:ℝ) ≤ 2*D*s := by linarith
  have hden : 0 < min a (1-a)*(m:ℝ) := mul_pos ht hmpos
  have hkden : 0 < min a (1-a)*kappa := mul_pos ht hkappa
  have hratio : 4*(hi-lo+(m:ℝ))/(min a (1-a)*(m:ℝ)) ≤
      8*D/(min a (1-a)*kappa) := by
    apply (div_le_div_iff₀ hden hkden).2
    have hw := mul_le_mul_of_nonneg_right hnum hkden.le
    have hd := mul_le_mul_of_nonneg_left hmlo (by positivity : 0 ≤ 8*D*min a (1-a))
    nlinarith
  refine ⟨J, M, v, hJ, ?_, hM, hinj, hnet, hgap, hfirstOnly, hlastOnly,
    hfirst, hlast, hcard, ?_, ?_⟩
  · linarith
  · linarith [hcard.trans_le hratio]
  · intro u hu
    obtain ⟨j, k, p, hlen, hend, hcentral, habs⟩ :=
      hattach u ((hJ u).mp hu).1 ((hJ u).mp hu).2
    refine ⟨j, (k.val, m-k.val), hlen, ?_, hcentral, habs⟩
    exact p.finish.symm.trans hend

end LPPDifferentiability
