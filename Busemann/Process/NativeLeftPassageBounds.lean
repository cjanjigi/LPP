/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.NativeStrictNorthBoundaryDeficit
public import Busemann.Process.HorizontalBoundaryCocycleBounds
public import Busemann.Process.VerticalBoundaryCocycleBounds
import Mathlib.Tactic

/-! Assemble two native passage-gradient bounds strictly left of one support face. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

/-- The native strict north exit deficit gives the horizontal lower and vertical
upper passage differences left of one extreme contact face (GRS 1510.00859v2,
Theorem 6.1, Step 1). The deficits at neighboring starts use one common event. -/
theorem ae_native_passage_difference_bounds_left_of_support_face
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
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hθface : ∀ ζ ∈ supportFace g h, θ < (ζ.1.1 : ℝ)) :
    ∀ᵐ s ∂P, ∀ x : Lattice, ∀ d : ℕ → ℕ × ℕ,
      (∀ n, (d n).1 + (d n).2 = n) →
      (∀ᶠ n : ℕ in atTop, ((d n).1 : ℝ) / (n : ℝ) ≤ θ) →
      ∀ᶠ n : ℕ in atTop, 0 < n ∧
        (0 < (d n).1 →
          B x (x + (1, 0)) s ≤
            lastPassage (processEnvironment s) x (d n) -
              lastPassage (processEnvironment s) (x + (1, 0))
                ((d n).1 - 1, (d n).2)) ∧
        (0 < (d n).2 →
          lastPassage (processEnvironment s) x (d n) -
              lastPassage (processEnvironment s) (x + (0, 1))
                ((d n).1, (d n).2 - 1) ≤
            B x (x + (0, 1)) s) := by
  classical
  have hθlt : θ < 1 := hθ1
  -- Choose a buffer strictly below the leftmost contact direction.
  obtain ⟨left, right, hleft, _, hleftMin, _, _⟩ :=
    ae_native_calibrated_endpoints_confined μ hmoment hnonconstant P hMarginal hShift
      B hB hInt hRec g hg η h hh hext hMean
  let τ : ℝ := (θ + (left.1.1 : ℝ)) / 2
  have hθleft : θ < (left.1.1 : ℝ) := hθface left hleft
  have hleftOne : (left.1.1 : ℝ) < 1 := by
    have hsum := left.2.2.2
    have hpositive : (0 : ℝ) < (left.1.2 : ℝ) := by exact_mod_cast left.2.2.1
    linarith
  have hθτ : θ < τ := by dsimp [τ]; linarith
  have hτ0 : 0 ≤ τ := le_trans hθ0 hθτ.le
  have hτ1 : τ < 1 := by dsimp [τ]; linarith only [hθlt, hθleft, hleftOne]
  have hτface : ∀ ζ ∈ supportFace g h, τ < (ζ.1.1 : ℝ) := by
    intro ζ hζ
    exact lt_of_lt_of_le (by dsimp [τ]; linarith : τ < (left.1.1 : ℝ))
      (hleftMin ζ hζ)
  have hNative := ae_native_strict_north_boundary_deficit
    μ hmoment hnonconstant P hMarginal hShift B hB hInt hRec
    g hg η h hh hext hMean τ hτ0 hτ1 hτface
  filter_upwards [hNative, hB.2.2, hRec] with s hs ha hr
  intro x d hlen hratio
  let D : ℕ → ℕ × ℕ := fun k =>
    if k = 0 then (0, 0) else ((d (k - 1)).1 + 1, (d (k - 1)).2)
  let T : ℕ → ℕ × ℕ := fun k =>
    if 0 < (d k).2 then ((d k).1 + 1, (d k).2 - 1) else (0, k)
  have hDsucc (n : ℕ) : D (n + 1) = ((d n).1 + 1, (d n).2) := by
    simp [D]
  have hDlen (k : ℕ) : (D k).1 + (D k).2 = k := by
    cases k with
    | zero => simp [D]
    | succ n =>
      simp only [hDsucc]
      have hd := hlen n
      omega
  have hTlen (k : ℕ) : (T k).1 + (T k).2 = k := by
    by_cases hk : 0 < (d k).2
    · simp only [T, hk, ↓reduceIte]
      have hd := hlen k
      omega
    · simp [T, hk]
  -- A single deterministic threshold absorbs the added east step in both ratios.
  have hbuffer : ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < (d n).2 ∧
        (((d n).1 : ℝ) + 1) / (n : ℝ) ≤ τ := by
    have hc : 0 < τ - θ := sub_pos.mpr hθτ
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / (τ - θ))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hratio
    apply eventually_atTop.mpr
    refine ⟨max 1 (max K N), ?_⟩
    intro n hn
    have hnpos : 0 < n := (le_max_left 1 (max K N)).trans hn
    have hnK : K ≤ n := (le_max_left K N).trans
      ((le_max_right 1 (max K N)).trans hn)
    have hnN : N ≤ n := (le_max_right K N).trans
      ((le_max_right 1 (max K N)).trans hn)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hdn : ((d n).1 : ℝ) ≤ θ * (n : ℝ) :=
      (div_le_iff₀ hnR).mp (hN n hnN)
    have hKR : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnK
    have hKbuffer : 1 ≤ (τ - θ) * (n : ℝ) := by
      have hKpos : (1 : ℝ) / (τ - θ) < (n : ℝ) := lt_of_lt_of_le hK hKR
      simpa only [mul_comm] using (div_le_iff₀ hc).mp hKpos.le
    have hdn2 : 0 < (d n).2 := by
      have hsum : ((d n).1 : ℝ) + ((d n).2 : ℝ) = (n : ℝ) := by
        exact_mod_cast hlen n
      have hsecond : (0 : ℝ) < ((d n).2 : ℝ) := by
        nlinarith only [hdn, hsum, hθlt, hnR]
      exact_mod_cast hsecond
    refine ⟨hnpos, hdn2, (div_le_iff₀ hnR).2 ?_⟩
    linarith only [hdn, hKbuffer]
  have hDratio : ∀ᶠ k : ℕ in atTop,
      ((D k).1 : ℝ) / (k : ℝ) ≤ τ := by
    obtain ⟨K, hK⟩ := eventually_atTop.mp hbuffer
    apply eventually_atTop.mpr
    refine ⟨K + 1, ?_⟩
    intro k hk
    cases k with
    | zero => omega
    | succ n =>
      have hnK : K ≤ n := by omega
      have hb := hK n hnK
      simp only [hDsucc, Nat.cast_add, Nat.cast_one]
      have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hnp : 0 < (n + 1 : ℝ) := by positivity
      apply (div_le_iff₀ hnp).2
      have hdle := (div_le_iff₀ (by exact_mod_cast hb.1 : 0 < (n : ℝ))).mp hb.2.2
      have hτnonneg : 0 ≤ τ := hτ0
      nlinarith only [hdle, hτnonneg]
  have hTratio : ∀ᶠ n : ℕ in atTop,
      ((T n).1 : ℝ) / (n : ℝ) ≤ τ := by
    filter_upwards [hbuffer] with n hn
    simpa only [T, hn.2.1, ↓reduceIte, Nat.cast_add, Nat.cast_one] using hn.2.2
  have hChildRatio : ∀ᶠ n : ℕ in atTop,
      ((d n).1 : ℝ) / (n : ℝ) ≤ τ := hratio.mono fun n hn => hn.trans hθτ.le
  have hDnative := hs x D hDlen hDratio
  have hHnative := hs (x + (1, 0)) d hlen hChildRatio
  have hVnative := hs (x + (0, 1)) T hTlen hTratio
  obtain ⟨KD, hKD⟩ := eventually_atTop.mp hDnative
  filter_upwards [hHnative, hVnative, hbuffer,
    eventually_ge_atTop (max 1 KD)] with n hH hV hb hn
  have hnpos : 0 < n := (le_max_left 1 KD).trans hn
  have hKDnext : KD ≤ n + 1 := by omega
  have hD := hKD (n + 1) hKDnext
  let dn : ℕ × ℕ := d n
  let v : Lattice := x + (((dn.1 + 1 : ℕ) : ℤ), (dn.2 : ℤ))
  let C : Lattice → Lattice → ℝ := fun u w => B u w s
  let ω : Environment := processEnvironment s
  let N : Environment := fun z =>
    if z.2 = v.2 ∧ z.1 < v.1 then C z (z + (1, 0)) else ω z
  have hDterminal : x + (((D (n + 1)).1 : ℤ), ((D (n + 1)).2 : ℤ)) = v := by
    simp only [hDsucc]
    rfl
  have hHterminal : x + (1, 0) + ((dn.1 : ℤ), (dn.2 : ℤ)) = v := by
    apply Prod.ext <;> simp only [v, dn, Prod.fst_add, Prod.snd_add] <;> omega
  have hTvalue : T n = (dn.1 + 1, dn.2 - 1) := by
    simp [T, dn, hb.2.1]
  have hVterminal : x + (0, 1) + (((T n).1 : ℤ), ((T n).2 : ℤ)) = v := by
    apply Prod.ext <;> simp only [hTvalue, v, dn, Prod.fst_add, Prod.snd_add] <;> omega
  -- All three native deficits use the same modified north field and terminal.
  have hFirst : lastPassage N x (dn.1 + 1, dn.2) < C x v := by
    have hd := hD.2
    rw [hDterminal] at hd
    simpa only [N, C, ω, hDsucc, dn] using hd
  have hHorizontalChild : lastPassage N (x + (1, 0)) dn < C (x + (1, 0)) v := by
    have hd := hH.2
    rw [hHterminal] at hd
    simpa only [N, C, ω, dn] using hd
  have hVerticalChild :
      lastPassage N (x + (0, 1)) (dn.1 + 1, dn.2 - 1) <
        C (x + (0, 1)) v := by
    have hd := hV.2
    rw [hVterminal] at hd
    simpa only [N, C, ω, hTvalue] using hd
  have hHorizontal (hd1 : 0 < dn.1) :
      C x (x + (1, 0)) ≤
        lastPassage ω x dn - lastPassage ω (x + (1, 0)) (dn.1 - 1, dn.2) := by
    have ha1 : dn.1 - 1 + 1 = dn.1 := by omega
    have ha2 : dn.1 - 1 + 2 = dn.1 + 1 := by omega
    have hfinite := horizontal_passage_difference_ge_cocycle_of_north_deficits
      ω C ha hr x (dn.1 - 1) dn.2
    simp only [ha1, ha2] at hfinite
    exact hfinite hFirst hHorizontalChild
  have hVertical (hd2 : 0 < dn.2) :
      lastPassage ω x dn - lastPassage ω (x + (0, 1)) (dn.1, dn.2 - 1) ≤
        C x (x + (0, 1)) := by
    have hb1 : dn.2 - 1 + 1 = dn.2 := by omega
    have hfinite := vertical_passage_difference_le_cocycle_of_north_deficits
      ω C ha hr x dn.1 (dn.2 - 1)
    simp only [hb1] at hfinite
    exact hfinite hFirst hVerticalChild
  exact ⟨hnpos, (by simpa only [C, ω, dn] using hHorizontal),
    (by simpa only [C, ω, dn] using hVertical)⟩

end LPP.Busemann
