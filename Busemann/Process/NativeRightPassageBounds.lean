/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.NativeStrictEastBoundaryDeficit
public import Busemann.Process.HorizontalBoundaryCocycleBounds
public import Busemann.Process.VerticalBoundaryCocycleBounds
import Mathlib.Tactic

/-! Neighboring-start passage bounds right of one support face. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

/-- The strict east deficit gives eventual horizontal upper and vertical lower
neighboring-start passage bounds to the right of one support face; see
GRS arXiv:1510.00859v2, Theorem 6.1, Step 1. -/
theorem ae_native_passage_difference_bounds_right_of_support_face
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (hRec : recovers_weight_map_ae P processEnvironment B)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (η : InteriorDirection) (h : SupportTilt g)
    (hh : SupportsAt g η h.1)
    (hext : (∀ k : SupportTilt g,
      SupportsAt g η k.1 → h.1.1 ≤ k.1.1) ∨
      (∀ k : SupportTilt g,
        SupportsAt g η k.1 → k.1.1 ≤ h.1.1))
    (hMean : ∀ i : Fin 2,
      (∫ s, B 0 (finiteEdgeStep i) s ∂P) =
        -finiteTiltCoordinate h.1 i)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθface : ∀ ζ ∈ supportFace g h, (ζ.1.1 : ℝ) < θ) :
    ∀ᵐ s ∂P, ∀ x : Lattice, ∀ d : ℕ → ℕ × ℕ,
      (∀ n, (d n).1 + (d n).2 = n) →
      (∀ᶠ n : ℕ in atTop, θ ≤ ((d n).1 : ℝ) / (n : ℝ)) →
      ∀ᶠ n : ℕ in atTop, 0 < n ∧
        (0 < (d n).1 →
          lastPassage (processEnvironment s) x (d n) -
              lastPassage (processEnvironment s) (x + (1, 0))
                ((d n).1 - 1, (d n).2) ≤
            B x (x + (1, 0)) s) ∧
        (0 < (d n).2 →
          B x (x + (0, 1)) s ≤
            lastPassage (processEnvironment s) x (d n) -
              lastPassage (processEnvironment s) (x + (0, 1))
                ((d n).1, (d n).2 - 1)) := by
  classical
  -- The confinement result supplies the right endpoint of this face.
  obtain ⟨_, right, _, hRight, _, hRightMax, _⟩ :=
    ae_native_calibrated_endpoints_confined μ hmoment hnonconstant P
      hMarginal hShift B hB hInt hRec g hg η h hh hext hMean
  let τ : ℝ := ((right.1.1 : ℝ) + θ) / 2
  have hrightpos : 0 < (right.1.1 : ℝ) := by
    exact_mod_cast right.2.1
  have hτpos : 0 < τ := by dsimp [τ]; linarith
  have hτθ : τ < θ := by
    dsimp [τ]
    linarith [hθface right hRight]
  have hτone : τ ≤ 1 := (le_of_lt hτθ).trans hθ1
  have hτface : ∀ ζ ∈ supportFace g h, (ζ.1.1 : ℝ) < τ := by
    intro ζ hζ
    exact lt_of_le_of_lt (hRightMax ζ hζ) (by dsimp [τ]; linarith [hθface right hRight])
  have hEast := ae_native_strict_east_boundary_deficit μ hmoment hnonconstant
    P hMarginal hShift B hB hInt hRec g hg η h hh hext hMean
    τ hτpos hτone hτface
  filter_upwards [hEast, hB.2.2, hRec] with s hs ha hr
  intro x d hlen hratio
  let D : ℕ → ℕ × ℕ := fun k =>
    match k with
    | 0 => (0, 0)
    | n + 1 => ((d n).1, (d n).2 + 1)
  let T : ℕ → ℕ × ℕ := fun n =>
    if 0 < (d n).1 then ((d n).1 - 1, (d n).2 + 1) else (n, 0)
  have hDlen : ∀ k, (D k).1 + (D k).2 = k := by
    intro k
    cases k with
    | zero => rfl
    | succ n =>
        have := hlen n
        dsimp [D]
        omega
  have hTlen : ∀ n, (T n).1 + (T n).2 = n := by
    intro n
    dsimp [T]
    split_ifs with hpos
    · have := hlen n
      omega
    · omega
  have hbuffer : 0 < θ - τ := by linarith [hτθ]
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / (θ - τ))
  have hKbuffer : 1 ≤ (θ - τ) * (K : ℝ) := by
    have h := (div_lt_iff₀ hbuffer).mp hK
    linarith
  obtain ⟨Nratio, hNratio⟩ := eventually_atTop.mp hratio
  have hRatioD : ∀ᶠ k : ℕ in atTop,
      τ ≤ ((D k).1 : ℝ) / (k : ℝ) := by
    filter_upwards [eventually_ge_atTop (max (Nratio + 1) (K + 2))] with k hk
    have hkpos : 0 < k := by omega
    let n := k - 1
    have hkn : k = n + 1 := by dsimp [n]; omega
    have hnratio : θ ≤ ((d n).1 : ℝ) / (n : ℝ) :=
      hNratio n (by dsimp [n]; omega)
    have hnpos : 0 < n := by dsimp [n]; omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hd1 : θ * (n : ℝ) ≤ ((d n).1 : ℝ) :=
      (le_div_iff₀ hnR).mp hnratio
    have hnK : K ≤ n := by dsimp [n]; omega
    have hnKR : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnK
    have hmargin : 1 ≤ (θ - τ) * (n : ℝ) :=
      hKbuffer.trans (mul_le_mul_of_nonneg_left hnKR hbuffer.le)
    have hkR : (k : ℝ) = (n : ℝ) + 1 := by exact_mod_cast hkn
    rw [hkn]
    change τ ≤ ((d n).1 : ℝ) / ((n + 1 : ℕ) : ℝ)
    apply (le_div_iff₀ (by exact_mod_cast (Nat.succ_pos n))).2
    push_cast
    nlinarith only [hd1, hmargin, hτone]
  have hRatioT : ∀ᶠ n : ℕ in atTop,
      τ ≤ ((T n).1 : ℝ) / (n : ℝ) := by
    filter_upwards [hratio, eventually_ge_atTop (max 1 K)] with n hnratio hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hd1 : θ * (n : ℝ) ≤ ((d n).1 : ℝ) :=
      (le_div_iff₀ hnR).mp hnratio
    have hd1pos : 0 < (d n).1 := by
      have hd1R : (0 : ℝ) < ((d n).1 : ℝ) :=
        lt_of_lt_of_le (mul_pos hθ0 hnR) hd1
      exact_mod_cast hd1R
    have hnK : K ≤ n := by omega
    have hnKR : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnK
    have hmargin : 1 ≤ (θ - τ) * (n : ℝ) :=
      hKbuffer.trans (mul_le_mul_of_nonneg_left hnKR hbuffer.le)
    simp only [T]
    simp [hd1pos]
    apply (le_div_iff₀ hnR).2
    nlinarith only [hd1, hmargin]
  have hRatioChild : ∀ᶠ n : ℕ in atTop,
      τ ≤ ((d n).1 : ℝ) / (n : ℝ) :=
    hratio.mono (fun n hn => le_trans (le_of_lt hτθ) hn)
  obtain ⟨ND, hND⟩ := eventually_atTop.mp (hs x D hDlen hRatioD)
  obtain ⟨NT, hNT⟩ := eventually_atTop.mp
    (hs (x + (1, 0)) T hTlen hRatioT)
  obtain ⟨NV, hNV⟩ := eventually_atTop.mp
    (hs (x + (0, 1)) d hlen hRatioChild)
  -- All three deficits hold at the common north-extended terminal.
  filter_upwards [hratio,
      eventually_ge_atTop (max 1 (max Nratio (max K (max ND (max NT NV)))))]
    with n hnratio hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hd1lower : θ * (n : ℝ) ≤ ((d n).1 : ℝ) :=
    (le_div_iff₀ hnR).mp hnratio
  have hd1pos : 0 < (d n).1 := by
    have hd1R : (0 : ℝ) < ((d n).1 : ℝ) :=
      lt_of_lt_of_le (mul_pos hθ0 hnR) hd1lower
    exact_mod_cast hd1R
  have hFirst := (hND (n + 1) (by omega)).2
  have hHorizontalChild := (hNT n (by omega)).2
  have hVerticalChild := (hNV n (by omega)).2
  let v : Lattice := x + (((d n).1 : ℤ), (((d n).2 + 1 : ℕ) : ℤ))
  let E : Environment := fun z =>
    if z.1 = v.1 ∧ z.2 < v.2 then B z (z + (0, 1)) s
    else processEnvironment s z
  have hFirstDeficit : lastPassage E x ((d n).1, (d n).2 + 1) < B x v s := by
    simpa only [D, E, v] using hFirst
  have hHorizontalDeficit :
      lastPassage E (x + (1, 0)) ((d n).1 - 1, (d n).2 + 1) <
        B (x + (1, 0)) v s := by
    have hterminal :
        x + (1, 0) + (((T n).1 : ℤ), ((T n).2 : ℤ)) = v := by
      simp [T, hd1pos]
      dsimp [v]
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]
      · omega
      · omega
    rw [hterminal] at hHorizontalChild
    simpa [T, hd1pos, E] using hHorizontalChild
  have hVerticalDeficit :
      lastPassage E (x + (0, 1)) (d n) <
        B (x + (0, 1)) v s := by
    have hterminal :
        x + (0, 1) + (((d n).1 : ℤ), ((d n).2 : ℤ)) = v := by
      apply Prod.ext <;> dsimp [v] <;> omega
    simpa only [hterminal, E] using hVerticalChild
  refine ⟨hnpos, ?_, ?_⟩
  · intro _
    have hcompare := horizontal_passage_difference_le_cocycle_of_east_deficits
      (processEnvironment s) (fun a b => B a b s) ha hr x
      ((d n).1 - 1) (d n).2
    have ha1 : (d n).1 - 1 + 1 = (d n).1 := Nat.sub_add_cancel (by omega)
    simp only [ha1] at hcompare
    simpa only [ha1, E, v] using hcompare hFirstDeficit hHorizontalDeficit
  · intro hd2pos
    have hcompare := vertical_passage_difference_ge_cocycle_of_east_deficits
      (processEnvironment s) (fun a b => B a b s) ha hr x
      (d n).1 ((d n).2 - 1)
    have hb1 : (d n).2 - 1 + 1 = (d n).2 := Nat.sub_add_cancel (by omega)
    have hb2 : (d n).2 - 1 + 2 = (d n).2 + 1 := by omega
    simp only [hb1, hb2] at hcompare
    simpa only [hb1, hb2, E, v] using hcompare hFirstDeficit hVerticalDeficit

end LPP.Busemann

end
