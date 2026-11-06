/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.ForwardNetAttachment
public import Differentiability.Model.Paths.BackwardNetAttachment
public import Differentiability.Analysis.AttachmentInteriority
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-! Finite signed level intervals and the converse attachment construction. -/
public section
namespace LPPDifferentiability

/-- Integer first coordinates describe a closed transverse interval exactly. -/
theorem level_interval_iff (a lo hi : ℝ) (I : ℤ) (u : Lattice) :
    (u.1 + u.2 = I ∧
      (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Set.Icc lo hi) ↔
    (u.2 = I-u.1 ∧ u.1 ∈ Finset.Icc (Int.ceil (lo+a*I)) (Int.floor (hi+a*I))) := by
  have hr (h : u.1+u.2=I) : (1-a)*(u.1:ℝ)-a*(u.2:ℝ) = (u.1:ℝ)-a*I := by
    have hh : (u.1:ℝ)+(u.2:ℝ)=(I:ℝ) := by exact_mod_cast h
    calc
      _ = (u.1:ℝ)-a*((u.1:ℝ)+(u.2:ℝ)) := by ring
      _ = _ := by rw [hh]
  simp only [Finset.mem_Icc, Int.ceil_le, Int.le_floor, Set.mem_Icc]
  constructor
  · rintro ⟨h,hlo,hhi⟩
    rw [hr h] at hlo hhi
    exact ⟨by omega, by linarith, by linarith⟩
  · rintro ⟨h,hlo,hhi⟩
    have hl : u.1+u.2=I := by omega
    rw [hr hl]
    exact ⟨hl, by linarith, by linarith⟩

/-- The actual lattice interval is finite and has at most width plus one sites. -/
theorem exists_finset_level_interval (a lo hi : ℝ) (I : ℤ) (hwidth : lo ≤ hi) :
    ∃ J : Finset Lattice,
      (∀ u, u ∈ J ↔ u.1+u.2=I ∧
        (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Set.Icc lo hi) ∧
      (J.card:ℝ) ≤ hi-lo+1 := by
  classical
  let l := Int.ceil (lo+a*I)
  let r := Int.floor (hi+a*I)
  let J := (Finset.Icc l r).image (fun x : ℤ => (x,I-x))
  have hmem (u : Lattice) : u ∈ J ↔ u.1+u.2=I ∧
      (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Set.Icc lo hi := by
    rw [level_interval_iff]
    constructor
    · intro hu
      obtain ⟨x,hx,hxu⟩ := Finset.mem_image.mp hu
      cases hxu
      exact ⟨rfl,hx⟩
    · rintro ⟨h,hx⟩
      exact Finset.mem_image.mpr ⟨u.1,hx,by ext <;> simp [h]⟩
  refine ⟨J,hmem,?_⟩
  have hinj : Function.Injective (fun x : ℤ => (x,I-x)) := fun _ _ h => congrArg Prod.fst h
  have hc : J.card = (Finset.Icc l r).card := Finset.card_image_of_injective _ hinj
  rw [hc]
  by_cases h : l ≤ r+1
  · have hcast := Int.card_Icc_of_le l r h
    have hcastR : ((Finset.Icc l r).card:ℝ) = (r:ℝ)+1-(l:ℝ) := by exact_mod_cast hcast
    rw [hcastR]
    have hlo : lo+a*I ≤ (l:ℝ) := Int.le_ceil _
    have hhi : (r:ℝ) ≤ hi+a*I := Int.floor_le _
    linarith
  · have hempty : Finset.Icc l r = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [hempty,Finset.card_empty,Nat.cast_zero]
    linarith

/-- Literal cone interior implies coordinatewise order for signed endpoints. -/
theorem level_cone_order (a theta : ℝ) (u v : Lattice)
    (htheta : 0 < theta) (hgap : 0 ≤ ((v.1+v.2-u.1-u.2:ℤ):ℝ))
    (hcone : |(1-a)*((v.1:ℝ)-(u.1:ℝ))-a*((v.2:ℝ)-(u.2:ℝ))| ≤
      (min a (1-a)-theta)*((v.1:ℝ)+(v.2:ℝ)-(u.1:ℝ)-(u.2:ℝ))) : u ≤ v := by
  have hgapR : 0 ≤ (v.1:ℝ)+(v.2:ℝ)-(u.1:ℝ)-(u.2:ℝ) := by exact_mod_cast hgap
  have h1 := mul_nonneg (sub_nonneg.mpr (min_le_left a (1-a))) hgapR
  have h2 := mul_nonneg (sub_nonneg.mpr (min_le_right a (1-a))) hgapR
  have ht := mul_nonneg htheta.le hgapR
  have hc := abs_le.mp hcone
  constructor
  · exact_mod_cast (show (u.1:ℝ) ≤ (v.1:ℝ) by nlinarith only [hc.1,h1,ht])
  · exact_mod_cast (show (u.2:ℝ) ≤ (v.2:ℝ) by nlinarith only [hc.2,h2,ht])

/-- Every lattice site in the expanded forward window comes from an actual
original endpoint, provided the original lattice interval is nonempty. -/
theorem exists_original_forward_attachment (a lo hi : ℝ) (I : ℤ) (m : ℕ)
    (hne : ∃ u : Lattice, u.1+u.2=I ∧
      (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Set.Icc lo hi)
    (w : Lattice) (hw : w.1+w.2=I+(m:ℤ))
    (hwr : (1-a)*(w.1:ℝ)-a*(w.2:ℝ) ∈
      Set.Icc (lo-a*m) (hi+(1-a)*m)) :
    ∃ (u : Lattice) (d : ℕ × ℕ) (p : Path u d),
      (u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Set.Icc lo hi) ∧
      d.1+d.2=m ∧ p.vertex (Fin.last (d.1+d.2))=w := by
  classical
  let l := Int.ceil (lo+a*I)
  let r := Int.floor (hi+a*I)
  obtain ⟨u0,hu0⟩ := hne
  have hu0' := (level_interval_iff a lo hi I u0).1 hu0
  have hlr : l ≤ r := (Finset.mem_Icc.mp hu0'.2).1.trans (Finset.mem_Icc.mp hu0'.2).2
  have hreal : (1-a)*(w.1:ℝ)-a*(w.2:ℝ) = (w.1:ℝ)-a*(I:ℝ)-a*(m:ℝ) := by
    have hh : (w.1:ℝ)+(w.2:ℝ)=(I:ℝ)+(m:ℝ) := by exact_mod_cast hw
    calc
      _ = (w.1:ℝ)-a*((w.1:ℝ)+(w.2:ℝ)) := by ring
      _ = _ := by rw [hh]; ring
  rw [hreal] at hwr
  have hwl : l ≤ w.1 := Int.ceil_le.mpr (by linarith [hwr.1])
  have hwr' : w.1 ≤ r+(m:ℤ) := by
    have hh : w.1-(m:ℤ) ≤ r := Int.le_floor.mpr (by push_cast; linarith [hwr.2])
    omega
  let k : ℤ := min w.1 r
  let u : Lattice := (k,I-k)
  have hku : u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Set.Icc lo hi := by
    apply (level_interval_iff a lo hi I u).2
    exact ⟨rfl,Finset.mem_Icc.mpr ⟨le_min hwl hlr,min_le_right _ _⟩⟩
  have horder : u ≤ w := by
    change k ≤ w.1 ∧ I-k ≤ w.2
    have hk : w.1-(m:ℤ) ≤ k := le_min (by omega) (by omega)
    exact ⟨min_le_left _ _,by omega⟩
  have hlevel : w.1+w.2=u.1+u.2+(m:ℤ) := by rw [hku.1]; exact hw
  obtain ⟨j,p,hp⟩ := exists_path_to_forwardReachable u w m
    ((forwardReachable_mem_iff u w m).2 ⟨horder,hlevel⟩)
  exact ⟨u,(j.val,m-j.val),p,hku,by have hj := j.isLt; omega,hp⟩

/-- The reverse expanded window has the analogous actual endpoint converse. -/
theorem exists_original_backward_attachment (a lo hi : ℝ) (I : ℤ) (m : ℕ)
    (hne : ∃ v : Lattice, v.1+v.2=I ∧
      (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Set.Icc lo hi)
    (w : Lattice) (hw : w.1+w.2=I-(m:ℤ))
    (hwr : (1-a)*(w.1:ℝ)-a*(w.2:ℝ) ∈
      Set.Icc (lo-(1-a)*m) (hi+a*m)) :
    ∃ (v : Lattice) (d : ℕ × ℕ) (p : Path w d),
      (v.1+v.2=I ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Set.Icc lo hi) ∧
      d.1+d.2=m ∧ p.vertex (Fin.last (d.1+d.2))=v := by
  classical
  let l := Int.ceil (lo+a*I)
  let r := Int.floor (hi+a*I)
  obtain ⟨v0,hv0⟩ := hne
  have hv0' := (level_interval_iff a lo hi I v0).1 hv0
  have hlr : l ≤ r := (Finset.mem_Icc.mp hv0'.2).1.trans (Finset.mem_Icc.mp hv0'.2).2
  have hreal : (1-a)*(w.1:ℝ)-a*(w.2:ℝ) = (w.1:ℝ)-a*(I:ℝ)+a*(m:ℝ) := by
    have hh : (w.1:ℝ)+(w.2:ℝ)=(I:ℝ)-(m:ℝ) := by exact_mod_cast hw
    calc
      _ = (w.1:ℝ)-a*((w.1:ℝ)+(w.2:ℝ)) := by ring
      _ = _ := by rw [hh]; ring
  rw [hreal] at hwr
  have hwl : l ≤ w.1+(m:ℤ) := Int.ceil_le.mpr (by push_cast; linarith [hwr.1])
  have hwr' : w.1 ≤ r := Int.le_floor.mpr (by linarith [hwr.2])
  let k : ℤ := max w.1 l
  let v : Lattice := (k,I-k)
  have hkv : v.1+v.2=I ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Set.Icc lo hi := by
    apply (level_interval_iff a lo hi I v).2
    exact ⟨rfl,Finset.mem_Icc.mpr ⟨le_max_right _ _,max_le hwr' hlr⟩⟩
  have horder : w ≤ v := by
    change w.1 ≤ k ∧ w.2 ≤ I-k
    have hk : k ≤ w.1+(m:ℤ) := max_le (by omega) hwl
    exact ⟨le_max_left _ _,by omega⟩
  have hlevel : v.1+v.2=w.1+w.2+(m:ℤ) := by rw [hkv.1,hw]; omega
  obtain ⟨j,p,hp⟩ := exists_path_to_forwardReachable w v m
    ((forwardReachable_mem_iff w v m).2 ⟨horder,hlevel⟩)
  exact ⟨v,(j.val,m-j.val),p,hkv,by have hj := j.isLt; omega,hp⟩

/-- The canonical natural displacement of two ordered signed sites has the
original difference as its cast and finishes exactly at the second site. -/
theorem ordered_lattice_displacement (u v : Lattice) (h : u ≤ v) :
    let d : ℕ × ℕ := ((v.1-u.1).toNat,(v.2-u.2).toNat)
    u+((d.1:ℤ),(d.2:ℤ))=v ∧
      (d.1:ℝ)=(v.1:ℝ)-(u.1:ℝ) ∧ (d.2:ℝ)=(v.2:ℝ)-(u.2:ℝ) := by
  have h1 : 0≤v.1-u.1 := sub_nonneg.mpr h.1
  have h2 : 0≤v.2-u.2 := sub_nonneg.mpr h.2
  have hc1 := Int.toNat_of_nonneg h1
  have hc2 := Int.toNat_of_nonneg h2
  dsimp only
  refine ⟨?_,?_,?_⟩
  · ext <;> simp only [Prod.fst_add,Prod.snd_add,hc1,hc2] <;> omega
  · exact_mod_cast hc1
  · exact_mod_cast hc2

/-- Removing two actual short attachments leaves every net pair in the
smaller cone. This uses only their literal transverse bounds. -/
theorem signed_middle_interiority (a theta s D : ℝ) (u w z v : Lattice)
    (I J : ℤ) (m : ℕ) (ht : 0<theta)
    (hs : 0<s)
    (hw : w.1+w.2=I+(m:ℤ)) (hz : z.1+z.2=J-(m:ℤ))
    (hlo : s≤((J-I:ℤ):ℝ)) (hhi : ((J-I:ℤ):ℝ)≤D*s)
    (hcone : |(1-a)*((v.1:ℝ)-(u.1:ℝ))-a*((v.2:ℝ)-(u.2:ℝ))| ≤
      (min a (1-a)-theta)*((J-I:ℤ):ℝ))
    (hfw : |(1-a)*((w.1:ℝ)-(u.1:ℝ))-a*((w.2:ℝ)-(u.2:ℝ))|≤(m:ℝ))
    (hbw : |(1-a)*((v.1:ℝ)-(z.1:ℝ))-a*((v.2:ℝ)-(z.2:ℝ))|≤(m:ℝ))
    (hcut1 : 2*(m:ℝ)≤s/4)
    (hcut2 : 2*(m:ℝ)*(1+min a (1-a)-theta/2)≤theta/2*s) :
    w≤z ∧ s/2≤(z.1:ℝ)+(z.2:ℝ)-(w.1:ℝ)-(w.2:ℝ) ∧
      (z.1:ℝ)+(z.2:ℝ)-(w.1:ℝ)-(w.2:ℝ)≤D*s ∧
      |(1-a)*((z.1:ℝ)-(w.1:ℝ))-a*((z.2:ℝ)-(w.2:ℝ))| ≤
        (min a (1-a)-theta/2)*
          ((z.1:ℝ)+(z.2:ℝ)-(w.1:ℝ)-(w.2:ℝ)) := by
  have hwr : (w.1:ℝ)+(w.2:ℝ)=(I:ℝ)+(m:ℝ) := by exact_mod_cast hw
  have hzr : (z.1:ℝ)+(z.2:ℝ)=(J:ℝ)-(m:ℝ) := by exact_mod_cast hz
  have heq : (z.1:ℝ)+(z.2:ℝ)-(w.1:ℝ)-(w.2:ℝ) = ((J-I:ℤ):ℝ)-2*(m:ℝ) := by
    push_cast
    linarith only [hwr,hzr]
  have hmidlo : s/2≤(z.1:ℝ)+(z.2:ℝ)-(w.1:ℝ)-(w.2:ℝ) := by
    rw [heq]; linarith only [hlo,hcut1,hs]
  have hmidhi : (z.1:ℝ)+(z.2:ℝ)-(w.1:ℝ)-(w.2:ℝ)≤D*s := by
    rw [heq]; linarith only [hhi,(Nat.cast_nonneg m : (0:ℝ)≤m)]
  have he : (1-a)*((z.1:ℝ)-(w.1:ℝ))-a*((z.2:ℝ)-(w.2:ℝ)) =
      ((1-a)*((v.1:ℝ)-(u.1:ℝ))-a*((v.2:ℝ)-(u.2:ℝ)))-
      ((1-a)*((w.1:ℝ)-(u.1:ℝ))-a*((w.2:ℝ)-(u.2:ℝ)))-
      ((1-a)*((v.1:ℝ)-(z.1:ℝ))-a*((v.2:ℝ)-(z.2:ℝ))) := by ring
  have hrho : |(1-a)*((z.1:ℝ)-(w.1:ℝ))-a*((z.2:ℝ)-(w.2:ℝ))| ≤
      (min a (1-a)-theta)*((J-I:ℤ):ℝ)+2*(m:ℝ) := by
    rw [he]
    have hab := abs_sub
      ((1-a)*((v.1:ℝ)-(u.1:ℝ))-a*((v.2:ℝ)-(u.2:ℝ)))
      ((1-a)*((w.1:ℝ)-(u.1:ℝ))-a*((w.2:ℝ)-(u.2:ℝ)))
    have habc := abs_sub
      (((1-a)*((v.1:ℝ)-(u.1:ℝ))-a*((v.2:ℝ)-(u.2:ℝ)))-
        ((1-a)*((w.1:ℝ)-(u.1:ℝ))-a*((w.2:ℝ)-(u.2:ℝ))))
      ((1-a)*((v.1:ℝ)-(z.1:ℝ))-a*((v.2:ℝ)-(z.2:ℝ)))
    linarith only [hab,habc,hcone,hfw,hbw]
  have hscale := mul_le_mul_of_nonneg_left hlo (show 0≤theta/2 by positivity)
  have hfinal : |(1-a)*((z.1:ℝ)-(w.1:ℝ))-a*((z.2:ℝ)-(w.2:ℝ))| ≤
      (min a (1-a)-theta/2)*((z.1:ℝ)+(z.2:ℝ)-(w.1:ℝ)-(w.2:ℝ)) := by
    rw [heq]
    nlinarith only [hrho,hscale,hcut2]
  refine ⟨level_cone_order a (theta/2) w z (by positivity) ?_ hfinal,hmidlo,hmidhi,hfinal⟩
  exact_mod_cast (show 0≤(z.1:ℝ)+(z.2:ℝ)-(w.1:ℝ)-(w.2:ℝ) by linarith only [hmidlo,hs])

/-- Actual path endpoints give the attachment bound in signed coordinates. -/
theorem path_attachment_transverse (a : ℝ) (ha : 0<a) (ha1 : a<1)
    (u w : Lattice) (d : ℕ × ℕ) (m : ℕ) (p : Path u d)
    (hm : d.1+d.2=m) (hf : p.vertex (Fin.last (d.1+d.2))=w) :
    |(1-a)*((w.1:ℝ)-(u.1:ℝ))-a*((w.2:ℝ)-(u.2:ℝ))|≤(m:ℝ) := by
  have hw : w=u+((d.1:ℤ),(d.2:ℤ)) := hf.symm.trans p.finish
  rw [hw]
  simpa only [Prod.fst_add,Prod.snd_add,Int.cast_add,Int.cast_natCast,
    add_sub_cancel_left] using attachment_transverse_bound a ha ha1 d m hm

/-- Every pair in the two expanded windows satisfies the middle travel
hypotheses. Converse attachments supply the original endpoints internally. -/
theorem expanded_interval_pair_displacement
    (a theta s D lo hi lo' hi' : ℝ) (I J : ℤ) (m : ℕ)
    (ha : 0<a) (ha1 : a<1) (ht : 0<theta) (hs : 0<s)
    (hne : ∃ u : Lattice, u.1+u.2=I ∧
      (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Set.Icc lo hi)
    (hne' : ∃ v : Lattice, v.1+v.2=J ∧
      (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Set.Icc lo' hi')
    (hlo : s≤((J-I:ℤ):ℝ)) (hhi : ((J-I:ℤ):ℝ)≤D*s)
    (hcone : ∀ u v : Lattice,
      (u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Set.Icc lo hi) →
      (v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Set.Icc lo' hi') →
      |(1-a)*((v.1:ℝ)-(u.1:ℝ))-a*((v.2:ℝ)-(u.2:ℝ))| ≤
        (min a (1-a)-theta)*((J-I:ℤ):ℝ))
    (hcut1 : 2*(m:ℝ)≤s/4)
    (hcut2 : 2*(m:ℝ)*(1+min a (1-a)-theta/2)≤theta/2*s)
    (w z : Lattice)
    (hw : w.1+w.2=I+(m:ℤ) ∧ (1-a)*(w.1:ℝ)-a*(w.2:ℝ) ∈
      Set.Icc (lo-a*m) (hi+(1-a)*m))
    (hz : z.1+z.2=J-(m:ℤ) ∧ (1-a)*(z.1:ℝ)-a*(z.2:ℝ) ∈
      Set.Icc (lo'-(1-a)*m) (hi'+a*m)) :
    let d : ℕ × ℕ := ((z.1-w.1).toNat,(z.2-w.2).toNat)
    w+((d.1:ℤ),(d.2:ℤ))=z ∧
      s/2≤((d.1+d.2:ℕ):ℝ) ∧ ((d.1+d.2:ℕ):ℝ)≤D*s ∧
      |(1-a)*(d.1:ℝ)-a*(d.2:ℝ)| ≤
        (min a (1-a)-theta/2)*((d.1:ℝ)+(d.2:ℝ)) := by
  obtain ⟨u,e₁,p,hu,he₁,hp⟩ := exists_original_forward_attachment a lo hi I m hne w hw.1 hw.2
  obtain ⟨v,e₂,r,hv,he₂,hr⟩ := exists_original_backward_attachment a lo' hi' J m hne' z hz.1 hz.2
  have hf := path_attachment_transverse a ha ha1 u w e₁ m p he₁ hp
  have hb := path_attachment_transverse a ha ha1 z v e₂ m r he₂ hr
  obtain ⟨hord,hml,hmh,hmc⟩ := signed_middle_interiority a theta s D u w z v I J m
    ht hs hw.1 hz.1 hlo hhi (hcone u v hu hv) hf hb hcut1 hcut2
  obtain ⟨hend,h1,h2⟩ := ordered_lattice_displacement w z hord
  refine ⟨hend,?_,?_,?_⟩
  · rw [Nat.cast_add,h1,h2]
    linarith only [hml]
  · rw [Nat.cast_add,h1,h2]
    linarith only [hmh]
  · rw [h1,h2]
    convert hmc using 1; ring

end LPPDifferentiability
