/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.RandomCocycle
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Integrability of cocycle increments

For a shift-covariant cocycle, integrability of the two origin unit increments
implies integrability of every signed increment.
-/

public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

private theorem integrable_shifted_cocycle_increment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : Lattice → Ω → Ω) (B : Lattice → Lattice → Ω → ℝ)
    (hT : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (hB : is_shift_covariant_cocycle P T B) (x d : Lattice)
    (hd : Integrable (B 0 d) P) : Integrable (B x (x + d)) P := by
  -- Shift covariance identifies this increment with a translate of the origin increment.
  have hcov : (fun ω => B x (x + d) ω) =ᵐ[P]
      (fun ω => B 0 d (T x ω)) := by
    filter_upwards [hB.2.1 0 d x] with ω hω
    simpa only [zero_add, add_comm d x] using hω
  have hcomp : Integrable (fun ω => B 0 d (T x ω)) P := by
    change Integrable ((fun ω => B 0 d ω) ∘ T x) P
    exact (hT x).integrable_comp_of_integrable hd
  exact hcomp.congr hcov.symm

private theorem integrable_extend_origin_increment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : Lattice → Ω → Ω) (B : Lattice → Lattice → Ω → ℝ)
    (hT : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (hB : is_shift_covariant_cocycle P T B) (x d : Lattice)
    (hx : Integrable (B 0 x) P) (hd : Integrable (B 0 d) P) :
    Integrable (B 0 (x + d)) P := by
  have hedge := integrable_shifted_cocycle_increment P T B hT hB x d hd
  -- Additivity expresses the longer increment as the old increment plus a shifted one.
  have hadd : (fun ω => B 0 x ω + B x (x + d) ω) =ᵐ[P]
      (fun ω => B 0 (x + d) ω) := by
    filter_upwards [hB.2.2] with ω hω
    exact hω 0 x (x + d)
  exact (hx.add hedge).congr hadd

private theorem lattice_eq_lower_add_nat_displacement
    (x u : Lattice) (hu₁ : u.1 ≤ x.1) (hu₂ : u.2 ≤ x.2) :
    ∃ m n : ℕ, x = u + ((m : ℤ), (n : ℤ)) := by
  refine ⟨(x.1 - u.1).toNat, (x.2 - u.2).toNat, ?_⟩
  have hm : ((x.1 - u.1).toNat : ℤ) = x.1 - u.1 :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hu₁)
  have hn : ((x.2 - u.2).toNat : ℤ) = x.2 - u.2 :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hu₂)
  apply Prod.ext
  · change x.1 = u.1 + ((x.1 - u.1).toNat : ℤ)
    calc
      x.1 = (x.1 - u.1) + u.1 := (sub_add_cancel _ _).symm
      _ = u.1 + ((x.1 - u.1).toNat : ℤ) := by rw [hm, add_comm]
  · change x.2 = u.2 + ((x.2 - u.2).toNat : ℤ)
    calc
      x.2 = (x.2 - u.2) + u.2 := (sub_add_cancel _ _).symm
      _ = u.2 + ((x.2 - u.2).toNat : ℤ) := by rw [hn, add_comm]

private theorem integrable_origin_nat_displacement
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : Lattice → Ω → Ω) (B : Lattice → Lattice → Ω → ℝ)
    (hT : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (hB : is_shift_covariant_cocycle P T B)
    (h₁ : Integrable (B 0 (1, 0)) P) (h₂ : Integrable (B 0 (0, 1)) P) :
    ∀ m n : ℕ, Integrable (B 0 ((m : ℤ), (n : ℤ))) P := by
  -- The cocycle identity at a repeated site makes the zero increment vanish almost everywhere.
  have hzero : (fun ω => B 0 0 ω) =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
    filter_upwards [hB.2.2] with ω hω
    have hadd := hω 0 0 0
    have hz : B 0 0 ω = 0 := by
      have hz' := congrArg (fun r : ℝ => r - B 0 0 ω) hadd
      simpa only [add_sub_cancel_right, sub_self] using hz'
    exact hz
  have hbase : Integrable (B 0 0) P := (integrable_zero Ω ℝ P).congr hzero.symm
  have hsite : ((0 : ℤ), (0 : ℤ)) = (0 : Lattice) := by
    ext <;> rfl
  -- Repeated vertical and horizontal steps cover the nonnegative quadrant.
  have hstep₂ : ∀ a b : ℕ,
      Integrable (B 0 ((a : ℤ), (b : ℤ))) P →
      Integrable (B 0 ((a : ℤ), ((b + 1 : ℕ) : ℤ))) P := by
    intro a b hab
    have hnext := integrable_extend_origin_increment P T B hT hB
      ((a : ℤ), (b : ℤ)) ((0 : ℤ), (1 : ℤ)) hab h₂
    change Integrable (B 0 ((a : ℤ), ((b + 1 : ℕ) : ℤ))) P
    simpa only [Prod.mk_add_mk, add_zero, Nat.cast_add, Nat.cast_one] using hnext
  have hvertical : ∀ b : ℕ, Integrable (B 0 ((0 : ℤ), (b : ℤ))) P := by
    intro b
    induction b with
    | zero => simpa only [Nat.cast_zero, hsite] using hbase
    | succ b ih => simpa only [Nat.cast_zero, Nat.succ_eq_add_one] using hstep₂ 0 b ih
  have hstep₁ : ∀ a b : ℕ,
      Integrable (B 0 ((a : ℤ), (b : ℤ))) P →
      Integrable (B 0 (((a + 1 : ℕ) : ℤ), (b : ℤ))) P := by
    intro a b hab
    have hnext := integrable_extend_origin_increment P T B hT hB
      ((a : ℤ), (b : ℤ)) ((1 : ℤ), (0 : ℤ)) hab h₁
    change Integrable (B 0 (((a + 1 : ℕ) : ℤ), (b : ℤ))) P
    simpa only [Prod.mk_add_mk, add_zero, zero_add, Nat.cast_add, Nat.cast_one] using hnext
  have hall : ∀ a b : ℕ, Integrable (B 0 ((a : ℤ), (b : ℤ))) P := by
    intro a
    induction a with
    | zero => simpa only [Nat.cast_zero] using hvertical
    | succ a ih =>
        intro b
        simpa only [Nat.succ_eq_add_one] using hstep₁ a b (ih b)
  exact hall

/-- If the two origin unit increments of a shift-covariant cocycle are integrable, then every
signed increment is integrable. This supplies the L1 extension used after Definition 4.1, reading
lines 776–785. -/
theorem integrable_cocycle_of_integrable_origin_edges
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : Lattice → Ω → Ω) (B : Lattice → Lattice → Ω → ℝ)
    (hT : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (hB : is_shift_covariant_cocycle P T B)
    (h₁ : Integrable (B 0 (1, 0)) P) (h₂ : Integrable (B 0 (0, 1)) P) :
    ∀ x y : Lattice, Integrable (B x y) P := by
  have hnat := integrable_origin_nat_displacement P T B hT hB h₁ h₂
  intro x y
  -- A coordinatewise lower site makes both displacements natural-valued.
  let u : Lattice := (min x.1 y.1, min x.2 y.2)
  have hxu₁ : u.1 ≤ x.1 := by dsimp [u]; exact min_le_left _ _
  have hxu₂ : u.2 ≤ x.2 := by dsimp [u]; exact min_le_left _ _
  have hyu₁ : u.1 ≤ y.1 := by dsimp [u]; exact min_le_right _ _
  have hyu₂ : u.2 ≤ y.2 := by dsimp [u]; exact min_le_right _ _
  obtain ⟨mx, nx, hx⟩ := lattice_eq_lower_add_nat_displacement x u hxu₁ hxu₂
  obtain ⟨my, ny, hy⟩ := lattice_eq_lower_add_nat_displacement y u hyu₁ hyu₂
  -- Translate the two nonnegative origin increments to the common lower site.
  have hux : Integrable (B u x) P := by
    rw [hx]
    exact integrable_shifted_cocycle_increment P T B hT hB u
      ((mx : ℤ), (nx : ℤ)) (hnat mx nx)
  have huy : Integrable (B u y) P := by
    rw [hy]
    exact integrable_shifted_cocycle_increment P T B hT hB u
      ((my : ℤ), (ny : ℤ)) (hnat my ny)
  -- Subtracting the two integrable lower-site increments gives the signed increment.
  have hrepresentation : (fun ω => B x y ω) =ᵐ[P]
      (fun ω => B u y ω - B u x ω) := by
    filter_upwards [hB.2.2] with ω hadd
    have h := hadd u x y
    calc
      B x y ω = (B u x ω + B x y ω) - B u x ω := by
        symm
        exact add_sub_cancel_left _ _
      _ = B u y ω - B u x ω := by rw [h]
  exact (huy.sub hux).congr hrepresentation.symm

end LPP.Busemann
