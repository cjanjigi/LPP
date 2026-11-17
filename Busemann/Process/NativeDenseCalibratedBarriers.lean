/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.NativeFullFamily
public import Busemann.Geometry.NativeGeometry
public import Busemann.Process.NativeCalibratedConfinement
public import Busemann.Process.RightmostPathGeodesic
public import Busemann.Frozen.Definitions.ApproachesFaceInterval
public import LPP_Foundations.Analysis.ShapeProfileCalculus
public import LPP_Foundations.Analysis.Quadrant
import Busemann.Geometry.DenseDifferentiabilityTilts
import Busemann.Process.FullEventCocycles
import Busemann.Process.Shifts
import Busemann.Process.RightmostPaths
import LPP_Foundations.Analysis.AbsoluteMomentShape
import Martin2004.Frozen.Martin.Shape
import Martin2004.Shape.MartinShapeExpectedRate
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import ProbabilityBasics.Probability.AbsoluteMomentTail
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.Tactic

@[expose] public section
open MeasureTheory ProbabilityTheory Filter LPPDifferentiability
open scoped ENNReal NNReal Topology BigOperators
namespace LPP.Busemann


private theorem direction_eq_fst (ξ η : InteriorDirection)
    (h : (ξ.1.1 : ℝ) = (η.1.1 : ℝ)) : ξ = η := by
  apply Subtype.ext
  apply Prod.ext
  · exact NNReal.coe_injective h
  · apply NNReal.coe_injective
    linarith only [ξ.2.2.2, η.2.2.2, h]

private theorem endpoints_of_interval (F : Set InteriorDirection)
    (l r a b : InteriorDirection)
    (hF : ∀ ζ, ζ ∈ F ↔ (l.1.1 : ℝ) ≤ (ζ.1.1 : ℝ) ∧ (ζ.1.1 : ℝ) ≤ (r.1.1 : ℝ))
    (ha : a ∈ F) (hb : b ∈ F)
    (hMin : ∀ ζ ∈ F, (a.1.1 : ℝ) ≤ (ζ.1.1 : ℝ))
    (hMax : ∀ ζ ∈ F, (ζ.1.1 : ℝ) ≤ (b.1.1 : ℝ)) : a = l ∧ b = r := by
  have hlr : (l.1.1 : ℝ) ≤ (r.1.1 : ℝ) := ((hF a).mp ha).1.trans ((hF a).mp ha).2
  have hl : l ∈ F := (hF l).mpr ⟨le_rfl, hlr⟩
  have hr : r ∈ F := (hF r).mpr ⟨hlr, le_rfl⟩
  exact ⟨direction_eq_fst a l (le_antisymm (hMin l hl) ((hF a).mp ha).1),
    direction_eq_fst b r (le_antisymm ((hF b).mp hb).2 (hMax r hr))⟩

private theorem actual_ray_confined
    (ω : Environment) (B : Lattice → Lattice → ℝ)
    (hAdd : is_additive B) (hRec : recovers_environment ω B)
    (left right : InteriorDirection)
    (hBands : ∀ x : Lattice, ∀ d : ℕ → ℕ × ℕ,
      (∀ n, (d n).1 + (d n).2 = n) →
      ∀ p : (n : ℕ) → LPPDifferentiability.Path x (d n),
        (∀ n, ∀ k : Fin ((d n).1 + (d n).2),
          B ((p n).vertex k.castSucc) ((p n).vertex k.succ) =
            ω ((p n).vertex k.castSucc)) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
          (left.1.1 : ℝ) - ε < ((d n).1 : ℝ) / (n : ℝ) ∧
          ((d n).1 : ℝ) / (n : ℝ) < (right.1.1 : ℝ) + ε)
    (x : Lattice) :
    let γ := rightmostCocyclePath B x
    IsLocallyRightmostGeodesic ω x γ ∧
    (∀ k : ℕ, B (γ k) (γ (k + 1)) = ω (γ k)) ∧
    ∃ d : ℕ → ℕ × ℕ,
      (∀ k, (d k).1 + (d k).2 = k ∧ γ k = x + (((d k).1 : ℤ), ((d k).2 : ℤ))) ∧
      approachesFaceInterval d left right := by
  classical
  let γ := rightmostCocyclePath B x
  have hCal (k : ℕ) : B (γ k) (γ (k + 1)) = ω (γ k) := by
    change B ((rightmostCocycleSuccessor B)^[k] x)
      ((rightmostCocycleSuccessor B)^[k + 1] x) = _
    rw [Function.iterate_succ_apply']
    exact rightmostCocycleSuccessor_calibrated ω B hRec _
  choose q hTrace _hPotential _hMaximum using exists_rightmostCocyclePath_prefix ω B hAdd hRec x
  let d (n : ℕ) : ℕ × ℕ := ((q n).1.val, n - (q n).1.val)
  let p (n : ℕ) : LPPDifferentiability.Path x (d n) := (q n).2
  have hLen (n : ℕ) : (d n).1 + (d n).2 = n := by
    have hlt := (q n).1.isLt
    dsimp only [d]
    omega
  have hVertex (n : ℕ) (i : Fin ((d n).1 + (d n).2 + 1)) :
      (p n).vertex i = γ i.val := hTrace n i.val i.isLt
  have hEnd (n : ℕ) : γ n = x + (((d n).1 : ℤ), ((d n).2 : ℤ)) := by
    have ht := hVertex n (Fin.last ((d n).1 + (d n).2))
    have htEnd : (p n).vertex (Fin.last ((d n).1 + (d n).2)) = γ n := by
      calc
        _ = γ ((d n).1 + (d n).2) := ht
        _ = γ n := congrArg γ (hLen n)
    exact htEnd.symm.trans (p n).finish
  have hPCal (n : ℕ) (k : Fin ((d n).1 + (d n).2)) :
      B ((p n).vertex k.castSucc) ((p n).vertex k.succ) = ω ((p n).vertex k.castSucc) := by
    rw [hVertex n k.castSucc, hVertex n k.succ]
    exact hCal k.val
  have hb := hBands x d hLen p hPCal
  let ρ (n : ℕ) : ℝ := ((d n).1 : ℝ) / (n : ℝ)
  have hBounds (n : ℕ) : 0 ≤ ρ n ∧ ρ n ≤ 1 := by
    by_cases hn : n = 0
    · subst n
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · dsimp only [ρ]
        rw [Nat.cast_zero, div_zero]
        exact zero_le_one
    · have hp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hd : (d n).1 ≤ n := by have := hLen n; omega
      exact ⟨div_nonneg (Nat.cast_nonneg _) hp.le,
        (div_le_iff₀ hp).mpr (by
          simpa only [one_mul] using
            (show ((d n).1 : ℝ) ≤ (n : ℝ) from by exact_mod_cast hd))⟩
  have hBelow : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) ρ :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun n => (hBounds n).1)
  have hAbove : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) ρ :=
    isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall fun n => (hBounds n).2)
  have hLeft : (left.1.1 : ℝ) ≤ liminf ρ atTop := by
    rw [Filter.le_liminf_iff hAbove.isCoboundedUnder_ge hBelow]
    intro t ht
    filter_upwards [hb ((left.1.1 : ℝ) - t) (sub_pos.mpr ht)] with n hn
    dsimp only [ρ]
    linarith only [hn.1]
  have hRight : limsup ρ atTop ≤ (right.1.1 : ℝ) := by
    rw [Filter.limsup_le_iff hBelow.isCoboundedUnder_le hAbove]
    intro t ht
    filter_upwards [hb (t - (right.1.1 : ℝ)) (sub_pos.mpr ht)] with n hn
    dsimp only [ρ]
    linarith only [hn.2]
  refine ⟨isLocallyRightmostGeodesic_rightmostCocyclePath ω B hAdd hRec x,
    hCal, d, fun n => ⟨hLen n, hEnd n⟩, ?_⟩
  change Tendsto (fun n => (d n).1 + (d n).2) atTop atTop ∧
    (left.1.1 : ℝ) ≤ liminf (fun n => ((d n).1 : ℝ) / (((d n).1 + (d n).2 : ℕ) : ℝ)) atTop ∧
    limsup (fun n => ((d n).1 : ℝ) / (((d n).1 + (d n).2 : ℕ) : ℝ)) atTop ≤ (right.1.1 : ℝ)
  simpa only [hLen] using
    (show Tendsto (fun n : ℕ => n) atTop atTop ∧
      (left.1.1 : ℝ) ≤ liminf ρ atTop ∧ limsup ρ atTop ≤ (right.1.1 : ℝ) from
        ⟨tendsto_id, hLeft, hRight⟩)

/-- The original real-law inputs give dense differentiability directions and
actual calibrated native barriers on one common event. GRS arXiv:1510.00860v1,
Theorem 2.1(i), Lemma 4.4(a); accepted Strong Existence, g400(a), line 1661.
This is a native barrier producer, prior to generic/physical/axis closure. -/
theorem exists_native_dense_differentiability_calibrated_barriers
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ g : Quadrant → ℝ, IsExpectedRateShape μ g ∧
    ∃ (D : ℕ → InteriorDirection)
      (hL hR : InteriorDirection → SupportTilt g)
      (leftEndpoint rightEndpoint : InteriorDirection → InteriorDirection),
      DenseRange D ∧
      (∀ n : ℕ, DifferentiableAt ℝ (quadrantExtension g)
        (quadrantInclusion (D n).1)) ∧
      (∀ ξ : InteriorDirection,
        SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
        ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
          (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1) ∧
      (∀ ξ : InteriorDirection,
        leftEndpoint ξ ∈ supportFacesUnion g (hL ξ) (hR ξ) ∧
        rightEndpoint ξ ∈ supportFacesUnion g (hL ξ) (hR ξ) ∧
        ∀ η : InteriorDirection,
          η ∈ supportFacesUnion g (hL ξ) (hR ξ) ↔
            (leftEndpoint ξ).1.1 ≤ η.1.1 ∧ η.1.1 ≤ (rightEndpoint ξ).1.1) ∧
      (∀ n : ℕ,
        hL (D n) = hR (D n) ∧
        (hL (D n)).1 =
          (-((fderiv ℝ (quadrantExtension g) (quadrantInclusion (D n).1)) ((1 : ℝ), 0)),
           -((fderiv ℝ (quadrantExtension g) (quadrantInclusion (D n).1)) (0, (1 : ℝ)))) ∧
        ∀ h : SupportTilt g, SupportsAt g (D n) h.1 → h = hL (D n)) ∧
      (∀ n : ℕ, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        (g (Real.toNNReal t, Real.toNNReal (1 - t)) +
            (hL (D n)).1.1 * t + (hL (D n)).1.2 * (1 - t) = 0 ↔
          ((leftEndpoint (D n)).1.1 : ℝ) ≤ t ∧
            t ≤ ((rightEndpoint (D n)).1.1 : ℝ))) ∧
    ∃ (P : Measure ProcessSample)
      (Bminus Bplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ)
      (C E : Set ProcessSample),

      (P Set.univ = 1 ∧
      P.map processEnvironment = environmentLaw μ ∧
      (∀ z : Lattice, P.map (processShift z) = P) ∧
      Measurable (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bminus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      Measurable (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bplus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      (∀ I : Set Lattice,
        ProbabilityTheory.IndepFun
          (futureVariables g I Bminus Bplus) (pastVariables I) P) ∧
      (∀ h : SupportTilt g, ∀ x y : Lattice,
        Integrable (Bminus h x y) P ∧ Integrable (Bplus h x y) P) ∧
      (∀ h : SupportTilt g, ∀ x : Lattice,
        (∫ s, Bminus h x (x + ((1 : ℤ), (0 : ℤ))) s ∂P) = -h.1.1 ∧
        (∫ s, Bplus h x (x + ((1 : ℤ), (0 : ℤ))) s ∂P) = -h.1.1 ∧
        (∫ s, Bminus h x (x + ((0 : ℤ), (1 : ℤ))) s ∂P) = -h.1.2 ∧
        (∫ s, Bplus h x (x + ((0 : ℤ), (1 : ℤ))) s ∂P) = -h.1.2) ∧
      MeasurableSet C ∧ P C = 1 ∧
      (∀ z : Lattice, ∀ s ∈ C, processShift z s ∈ C) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y z : Lattice,
        Bminus h (x + z) (y + z) s = Bminus h x y (processShift z s) ∧
        Bplus h (x + z) (y + z) s = Bplus h x y (processShift z s) ∧
        Bminus h x y s + Bminus h y z s = Bminus h x z s ∧
        Bplus h x y s + Bplus h y z s = Bplus h x z s) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g,
        recovers_environment (processEnvironment s) (fun x y => Bminus h x y s) ∧
        recovers_environment (processEnvironment s) (fun x y => Bplus h x y s)) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x : Lattice,
        Bminus h x (x + ((1 : ℤ), (0 : ℤ))) s ≥
          Bplus h x (x + ((1 : ℤ), (0 : ℤ))) s ∧
        Bminus h x (x + ((0 : ℤ), (1 : ℤ))) s ≤
          Bplus h x (x + ((0 : ℤ), (1 : ℤ))) s) ∧
      (∀ s ∈ C, ∀ h h' : SupportTilt g, h.1.1 < h'.1.1 → ∀ x : Lattice,
        Bplus h x (x + ((1 : ℤ), (0 : ℤ))) s ≥
          Bminus h' x (x + ((1 : ℤ), (0 : ℤ))) s ∧
        Bplus h x (x + ((0 : ℤ), (1 : ℤ))) s ≤
          Bminus h' x (x + ((0 : ℤ), (1 : ℤ))) s) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y : Lattice,
        ∀ hs : ℕ → SupportTilt g,
          (∀ n, (hs n).1.1 < h.1.1) → Tendsto hs atTop (𝓝 h) →
            Tendsto (fun n => Bminus (hs n) x y s) atTop (𝓝 (Bminus h x y s)) ∧
            Tendsto (fun n => Bplus (hs n) x y s) atTop (𝓝 (Bminus h x y s))) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y : Lattice,
        ∀ hs : ℕ → SupportTilt g,
          (∀ n, h.1.1 < (hs n).1.1) → Tendsto hs atTop (𝓝 h) →
            Tendsto (fun n => Bminus (hs n) x y s) atTop (𝓝 (Bplus h x y s)) ∧
            Tendsto (fun n => Bplus (hs n) x y s) atTop (𝓝 (Bplus h x y s))) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y : Lattice,
        Bminus h x y s = Bplus h x y s →
        ∀ hs : ℕ → SupportTilt g, Tendsto hs atTop (𝓝 h) →
          Tendsto (fun n => Bminus (hs n) x y s) atTop (𝓝 (Bminus h x y s)) ∧
          Tendsto (fun n => Bplus (hs n) x y s) atTop (𝓝 (Bminus h x y s))) ∧
      (∀ h : SupportTilt g, ∃ E : Set ProcessSample,
        MeasurableSet E ∧ E ⊆ C ∧ P E = 1 ∧
        ∀ s ∈ E, ∀ x y : Lattice,
          Bminus h x y s = Bplus h x y s)) ∧
      MeasurableSet E ∧ E ⊆ C ∧ P E = 1 ∧
      (∀ s ∈ E, ∀ n : ℕ, ∀ x y : Lattice,
        Bminus (hL (D n)) x y s = Bplus (hL (D n)) x y s) ∧
      ∀ s ∈ E, ∀ n : ℕ, ∀ sign : Bool, ∀ x : Lattice,
        let B : Lattice → Lattice → ℝ :=
          if sign then (fun a b => Bplus (hL (D n)) a b s)
          else (fun a b => Bminus (hL (D n)) a b s)
        let γ : ℕ → Lattice := rightmostCocyclePath B x
        IsLocallyRightmostGeodesic (processEnvironment s) x γ ∧
        (∀ k : ℕ, B (γ k) (γ (k + 1)) = processEnvironment s (γ k)) ∧
        ∃ d : ℕ → ℕ × ℕ,
          (∀ k : ℕ, (d k).1 + (d k).2 = k ∧
            γ k = x + (((d k).1 : ℤ), ((d k).2 : ℤ))) ∧
          approachesFaceInterval d (leftEndpoint (D n)) (rightEndpoint (D n)) := by
  classical
  have hMomentSource := hmoment
  obtain ⟨p, hp, hpm⟩ := hMomentSource
  have hPos := ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment μ hp hpm
  have hNeg := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment μ hp hpm
  obtain ⟨g, hgMartin, _⟩ := LPPDifferentiability.exists_unique_shape_martin μ hNeg hPos.2
  have hg : IsExpectedRateShape μ g :=
    LPPDifferentiability.Martin.martin_shape_tendsto_expected_rate μ hNeg hPos.2 g hgMartin
  have hGeometry := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hHom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z := hGeometry.2.1
  have hConc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y) := hGeometry.2.2
  have hNonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c := by
    rintro ⟨c, hc⟩
    exact (ne_of_lt (hμ c)) ((mem_ae_iff_prob_eq_one (measurableSet_singleton c)).mp hc)
  obtain ⟨D, hDense, hDiff⟩ := exists_dense_differentiability_directions g hConc hHom
  obtain ⟨hL, hR, left, right, hExt, hInterval⟩ :=
    exists_native_extreme_tilts_and_face_endpoints μ hμ hmoment g hg
  have hLR (ξ : InteriorDirection) : (left ξ).1.1 ≤ (right ξ).1.1 := by
    have hs : ξ ∈ supportFacesUnion g (hL ξ) (hR ξ) := Or.inl (hExt ξ).1
    exact ((hInterval ξ ξ).mp hs).1.trans ((hInterval ξ ξ).mp hs).2
  have hEndpoints (ξ : InteriorDirection) :
      left ξ ∈ supportFacesUnion g (hL ξ) (hR ξ) ∧
      right ξ ∈ supportFacesUnion g (hL ξ) (hR ξ) ∧
      ∀ η, η ∈ supportFacesUnion g (hL ξ) (hR ξ) ↔
        (left ξ).1.1 ≤ η.1.1 ∧ η.1.1 ≤ (right ξ).1.1 :=
    ⟨(hInterval ξ (left ξ)).mpr ⟨le_rfl, hLR ξ⟩,
      (hInterval ξ (right ξ)).mpr ⟨hLR ξ, le_rfl⟩, hInterval ξ⟩
  have hGradVal (n : ℕ) (h : SupportTilt g) (hh : SupportsAt g (D n) h.1) :=
    supporting_tilt_eq_negative_fderiv g hConc hHom (D n) (hDiff n) h hh
  have hEqual (n : ℕ) : hL (D n) = hR (D n) := by
    apply Subtype.ext
    exact (hGradVal n (hL (D n)) (hExt (D n)).1).trans
      (hGradVal n (hR (D n)) (hExt (D n)).2.1).symm
  have hUnique (n : ℕ) (h : SupportTilt g) (hh : SupportsAt g (D n) h.1) : h = hL (D n) := by
    apply Subtype.ext
    exact (hGradVal n h hh).trans (hGradVal n (hL (D n)) (hExt (D n)).1).symm
  have hFace (n : ℕ) (η : InteriorDirection) :
      η ∈ supportFace g (hL (D n)) ↔
        ((left (D n)).1.1 : ℝ) ≤ (η.1.1 : ℝ) ∧ (η.1.1 : ℝ) ≤ ((right (D n)).1.1 : ℝ) := by
    have hI := hInterval (D n) η
    rw [← hEqual n, supportFacesUnion, Set.union_self] at hI
    constructor
    · intro hη
      obtain ⟨hl, hr⟩ := hI.mp hη
      exact ⟨by exact_mod_cast hl, by exact_mod_cast hr⟩
    · rintro ⟨hl, hr⟩
      exact hI.mpr ⟨by exact_mod_cast hl, by exact_mod_cast hr⟩
  have hContact (n : ℕ) : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      (g (Real.toNNReal t, Real.toNNReal (1 - t)) +
        (hL (D n)).1.1 * t + (hL (D n)).1.2 * (1 - t) = 0 ↔
      ((left (D n)).1.1 : ℝ) ≤ t ∧ t ≤ ((right (D n)).1.1 : ℝ)) := by
    have gaps := support_tilt_strict_axis_gaps_of_absolute_moment μ hmoment hNonconstant g hg (hL (D n))
    obtain ⟨a, b, ha, hb, hmin, hmax, hc⟩ :=
      exists_support_face_interval_with_contact_characterization
        g hGeometry.1 hConc hHom (hL (D n)) gaps.1 gaps.2
    obtain ⟨rfl, rfl⟩ := endpoints_of_interval _ (left (D n)) (right (D n)) a b (hFace n) ha hb hmin hmax
    exact hc
  obtain ⟨P, Bminus, Bplus, C, hNative⟩ := exists_native_full_family μ hμ hmoment g hg
  have hNativeKeep := hNative
  rcases hNative with ⟨hProb, hMarginal, hStationary, hMeasM, hMeasP, _hFuture, hInt,
    hMeans, hCMeas, hCProb, _hCInv, hCoc, hRecovery, _hWithin, _hCross,
    _hBelow, _hAbove, _hAtEqual, hFixed⟩
  let : IsProbabilityMeasure P := (isProbabilityMeasure_iff).mpr hProb
  have hShift (z : Lattice) : MeasurePreserving (processShift z) P P :=
    ⟨measurable_processShift z, hStationary z⟩
  have hCM := cocycle_and_recovery_ae_of_full_event g P Bminus C hCMeas hCProb hMeasM
    (fun s hs h x y z => ⟨(hCoc s hs h x y z).1, (hCoc s hs h x y z).2.2.1⟩)
    (fun s hs h => (hRecovery s hs h).1)
  have hCP := cocycle_and_recovery_ae_of_full_event g P Bplus C hCMeas hCProb hMeasP
    (fun s hs h x y z => ⟨(hCoc s hs h x y z).2.1, (hCoc s hs h x y z).2.2.2⟩)
    (fun s hs h => (hRecovery s hs h).2)
  let F (b : Bool) := if b then Bplus else Bminus
  have hConf (n : ℕ) (b : Bool) : ∀ᵐ s ∂P, ∀ x : Lattice, ∀ d : ℕ → ℕ × ℕ,
      (∀ k, (d k).1 + (d k).2 = k) →
      ∀ q : (k : ℕ) → LPPDifferentiability.Path x (d k),
        (∀ k, ∀ j : Fin ((d k).1 + (d k).2),
          F b (hL (D n)) ((q k).vertex j.castSucc) ((q k).vertex j.succ) s =
            processEnvironment s ((q k).vertex j.castSucc)) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
          ((left (D n)).1.1 : ℝ) - ε < ((d k).1 : ℝ) / (k : ℝ) ∧
          ((d k).1 : ℝ) / (k : ℝ) < ((right (D n)).1.1 : ℝ) + ε := by
    have hc : is_shift_covariant_cocycle P processShift (F b (hL (D n))) := by
      cases b
      · exact (hCM (hL (D n))).1
      · exact (hCP (hL (D n))).1
    have hr : recovers_weight_map_ae P processEnvironment (F b (hL (D n))) := by
      cases b
      · exact (hCM (hL (D n))).2
      · exact (hCP (hL (D n))).2
    have hi : ∀ x y, Integrable (F b (hL (D n)) x y) P := by
      cases b
      · exact fun x y => (hInt (hL (D n)) x y).1
      · exact fun x y => (hInt (hL (D n)) x y).2
    have hm : ∀ i : Fin 2, (∫ s, F b (hL (D n)) 0 (finiteEdgeStep i) s ∂P) =
        -finiteTiltCoordinate (hL (D n)).1 i := by
      cases b
      · intro i
        fin_cases i
        · exact (hMeans (hL (D n)) 0).1
        · exact (hMeans (hL (D n)) 0).2.2.1
      · intro i
        fin_cases i
        · exact (hMeans (hL (D n)) 0).2.1
        · exact (hMeans (hL (D n)) 0).2.2.2
    obtain ⟨a, z, ha, hz, hmin, hmax, hae⟩ := ae_native_calibrated_endpoints_confined
      μ hmoment hNonconstant P hMarginal hShift (F b (hL (D n))) hc hi hr
      g hg (D n) (hL (D n)) (hExt (D n)).1
      (Or.inl (fun k hk => ((hExt (D n)).2.2 k hk).1)) hm
    obtain ⟨heq, hzEq⟩ := endpoints_of_interval _ (left (D n)) (right (D n)) a z (hFace n) ha hz hmin hmax
    rw [heq, hzEq] at hae
    exact hae
  have hCAE : ∀ᵐ s ∂P, s ∈ C := (mem_ae_iff_prob_eq_one hCMeas).mpr hCProb
  have hEqAE : ∀ᵐ s ∂P, ∀ n : ℕ, ∀ x y : Lattice,
      Bminus (hL (D n)) x y s = Bplus (hL (D n)) x y s := by
    apply ae_all_iff.mpr
    intro n
    obtain ⟨A, hAMeas, _hAC, hAProb, hAEq⟩ := hFixed (hL (D n))
    filter_upwards [(mem_ae_iff_prob_eq_one hAMeas).mpr hAProb] with s hs
    exact hAEq s hs
  have hRaysAE : ∀ᵐ s ∂P, ∀ n : ℕ, ∀ sign : Bool, ∀ x : Lattice,
      let B : Lattice → Lattice → ℝ :=
        if sign then (fun a b => Bplus (hL (D n)) a b s)
        else (fun a b => Bminus (hL (D n)) a b s)
      let γ := rightmostCocyclePath B x
      IsLocallyRightmostGeodesic (processEnvironment s) x γ ∧
      (∀ k : ℕ, B (γ k) (γ (k + 1)) = processEnvironment s (γ k)) ∧
      ∃ d : ℕ → ℕ × ℕ,
        (∀ k, (d k).1 + (d k).2 = k ∧ γ k = x + (((d k).1 : ℤ), ((d k).2 : ℤ))) ∧
        approachesFaceInterval d (left (D n)) (right (D n)) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro sign
    filter_upwards [hCAE, hConf n sign] with s hs hconf
    intro x
    have haM : is_additive (fun a b => Bminus (hL (D n)) a b s) :=
      fun a b c => (hCoc s hs (hL (D n)) a b c).2.2.1
    have haP : is_additive (fun a b => Bplus (hL (D n)) a b s) :=
      fun a b c => (hCoc s hs (hL (D n)) a b c).2.2.2
    cases sign
    · exact actual_ray_confined (processEnvironment s) _ haM
        (hRecovery s hs (hL (D n))).1 (left (D n)) (right (D n)) hconf x
    · exact actual_ray_confined (processEnvironment s) _ haP
        (hRecovery s hs (hL (D n))).2 (left (D n)) (right (D n)) hconf x
  have hAll := hCAE.and (hEqAE.and hRaysAE)
  obtain ⟨E, hEAE, hEMeas, hEGood⟩ := hAll.exists_measurable_mem
  refine ⟨g, hg, D, hL, hR, left, right, hDense, hDiff, hExt, hEndpoints, ?_, hContact,
    P, Bminus, Bplus, C, E, hNativeKeep, hEMeas,
    (fun s hs => (hEGood s hs).1), (mem_ae_iff_prob_eq_one hEMeas).mp hEAE,
    (fun s hs => (hEGood s hs).2.1), (fun s hs => (hEGood s hs).2.2)⟩
  intro n
  exact ⟨hEqual n, hGradVal n (hL (D n)) (hExt (D n)).1, hUnique n⟩

end LPP.Busemann
