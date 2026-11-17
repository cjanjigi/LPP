/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.GeneralizedBusemann
public import Busemann.Frozen.Definitions.CoalescingRightmostPaths
public import Busemann.Process.RealQuantileCoalescence
public import Busemann.Process.CoalescingGeodesicCocycle
public import Busemann.Geometry.CalibratedRightmostFamily
public import Busemann.Process.CoalescingRayCocycleOrder
public import Busemann.Process.RealQuantileFieldJointLaw
public import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
public import LPP_Foundations.Model.Paths.Coalescence
public import LPP_Foundations.Model.LatticeEdgeIntegration
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order.Basic
import Lean.Elab.Tactic.Omega

@[expose] public section
open MeasureTheory Filter ProbabilityTheory LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- An almost-everywhere property of a unit-interval parameter has a countable
dense set of actual witnesses.
Source: Strong Existence, proof of lm:orig_space, lines 1094–1095. -/
theorem countable_dense_subset_of_ae_unitInterval
    (G : unitInterval → Prop)
    (hG : ∀ᵐ s ∂(volume : Measure unitInterval), G s) :
    ∃ D : Set unitInterval, D.Countable ∧ Dense D ∧ ∀ s ∈ D, G s := by
  classical
  let : Measure.IsOpenPosMeasure (volume : Measure unitInterval) := {
    open_pos := by
      intro U hU hne
      obtain ⟨x, y, hxy, hIooU⟩ := hU.exists_Ioo_subset hne
      have hxyReal : (x : ℝ) < (y : ℝ) := hxy
      have hIooPos : 0 < (volume : Measure unitInterval) (Set.Ioo x y) := by
        rw [unitInterval.volume_Ioo]
        exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxyReal)
      exact ne_of_gt (lt_of_lt_of_le hIooPos (measure_mono hIooU)) }
  have hDenseG : Dense {s : unitInterval | G s} :=
    (volume : Measure unitInterval).dense_of_ae hG
  obtain ⟨D, hDG, hCount, hDenseD⟩ :=
    hDenseG.exists_countable_dense_subset
  exact ⟨D, hCount, hDenseD, fun s hs => hDG hs⟩
/-- Ordered canonical paths and equal integrable edge means identify both
coalescing fields on every signed pair.
Source: Strong Existence, proof of lm:orig_space, lines 1097–1098. -/
theorem ae_eq_of_ordered_coalescing_fields_with_same_edge_means
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (C D : Lattice → Lattice → Environment → ℝ)
    (hC : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) C)
    (hD : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) D)
    (hCoalC : HasCoalescingRightmostPaths (environmentLaw μ) C)
    (hCoalD : HasCoalescingRightmostPaths (environmentLaw μ) D)
    (hMeansEast :
      (∫ ω, C 0 (1, 0) ω ∂environmentLaw μ) =
        ∫ ω, D 0 (1, 0) ω ∂environmentLaw μ)
    (hMeansNorth :
      (∫ ω, C 0 (0, 1) ω ∂environmentLaw μ) =
        ∫ ω, D 0 (0, 1) ω ∂environmentLaw μ)
    (hPaths : ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
      pathSoutheastLE
        (rightmostCocyclePath (fun x y => C x y ω) u)
        (rightmostCocyclePath (fun x y => D x y ω) u)) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ x y : Lattice,
      C x y ω = D x y ω := by
  classical
  let east : Lattice := (1, 0)
  let north : Lattice := (0, 1)
  have hOrder := ae_cocycle_opposite_edge_order_of_rightmostPath_order
    μ C D hC hD hCoalC hCoalD hPaths
  have hTranslatedMean
      (F : Lattice → Lattice → Environment → ℝ)
      (hF : is_shift_covariant_cocycle (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) F)
      (x e : Lattice) (hInt : Integrable (F 0 e) (environmentLaw μ)) :
      (∫ ω, F x (x + e) ω ∂environmentLaw μ) =
        ∫ ω, F 0 e ω ∂environmentLaw μ := by
    have hShift := measurePreserving_environmentTranslationEquiv μ x
    have hCov : (fun ω => F x (x + e) ω) =ᵐ[environmentLaw μ]
        (fun ω => F 0 e (environmentTranslationEquiv x ω)) := by
      filter_upwards [hF.2.1 0 e x] with ω hω
      simpa only [zero_add, add_comm e x] using hω
    calc
      (∫ ω, F x (x + e) ω ∂environmentLaw μ) =
          ∫ ω, F 0 e (environmentTranslationEquiv x ω) ∂environmentLaw μ :=
        integral_congr_ae hCov
      _ = ∫ ω, F 0 e ω ∂environmentLaw μ :=
        hShift.integral_comp' (F 0 e)
  have hEastEq : ∀ᵐ ω ∂environmentLaw μ, ∀ x : Lattice,
      C x (x + east) ω = D x (x + east) ω := by
    apply ae_all_iff.mpr
    intro x
    have hLe : (fun ω => D x (x + east) ω) ≤ᵐ[environmentLaw μ]
        (fun ω => C x (x + east) ω) := by
      filter_upwards [hOrder] with ω hω
      exact (hω x).1
    have hMean :
        (∫ ω, D x (x + east) ω ∂environmentLaw μ) =
          ∫ ω, C x (x + east) ω ∂environmentLaw μ := by
      rw [hTranslatedMean D hD.1 x east (hD.2.2 0 east),
        hTranslatedMean C hC.1 x east (hC.2.2 0 east)]
      exact hMeansEast.symm
    exact ((integral_eq_iff_of_ae_le (hD.2.2 x (x + east))
      (hC.2.2 x (x + east)) hLe).mp hMean).symm
  have hNorthEq : ∀ᵐ ω ∂environmentLaw μ, ∀ x : Lattice,
      C x (x + north) ω = D x (x + north) ω := by
    apply ae_all_iff.mpr
    intro x
    have hLe : (fun ω => C x (x + north) ω) ≤ᵐ[environmentLaw μ]
        (fun ω => D x (x + north) ω) := by
      filter_upwards [hOrder] with ω hω
      exact (hω x).2
    have hMean :
        (∫ ω, C x (x + north) ω ∂environmentLaw μ) =
          ∫ ω, D x (x + north) ω ∂environmentLaw μ := by
      rw [hTranslatedMean C hC.1 x north (hC.2.2 0 north),
        hTranslatedMean D hD.1 x north (hD.2.2 0 north)]
      exact hMeansNorth
    exact (integral_eq_iff_of_ae_le (hC.2.2 x (x + north))
      (hD.2.2 x (x + north)) hLe).mp hMean
  filter_upwards [hEastEq, hNorthEq, hC.1.2.2, hD.1.2.2]
    with ω hEast hNorth hAddC hAddD
  let E : Lattice → Fin 2 → ℝ := fun x i => C x (x + finiteEdgeStep i) ω
  have hCurl : ∀ x, E x 0 + E (x + (1, 0)) 1 =
      E x 1 + E (x + (0, 1)) 0 := by
    intro x
    have hEastSquare := hAddC x (x + east) (x + (1, 1))
    have hNorthSquare := hAddC x (x + north) (x + (1, 1))
    have hEastStep : (x + east) + north = x + (1, 1) := by
      ext <;> simp [east, north, Prod.mk_add_mk, add_assoc]
    have hNorthStep : (x + north) + east = x + (1, 1) := by
      ext <;> simp [east, north, Prod.mk_add_mk, add_assoc]
    dsimp [E, finiteEdgeStep]
    rw [hEastStep, hNorthStep]
    linarith only [hEastSquare, hNorthSquare]
  obtain ⟨F, _, _, _, hUnique⟩ := exists_unique_lattice_edge_extension E hCurl
  have hCEdges (x : Lattice) :
      C x (x + (1, 0)) ω = E x 0 ∧
      C x (x + (0, 1)) ω = E x 1 := by
    constructor <;> simp [E, finiteEdgeStep]
  have hDEdges (x : Lattice) :
      D x (x + (1, 0)) ω = E x 0 ∧
      D x (x + (0, 1)) ω = E x 1 := by
    constructor
    · simpa [E, finiteEdgeStep] using (hEast x).symm
    · simpa [E, finiteEdgeStep] using (hNorth x).symm
  have hCF : (fun x y => C x y ω) = F := hUnique _ hAddC hCEdges
  have hDF : (fun x y => D x y ω) = F := hUnique _ hAddD hDEdges
  have hCD := hCF.trans hDF.symm
  intro x y
  exact congrFun (congrFun hCD x) y
/-- One fixed field's passage limits on a common positive quantile family
identify the raw field at product-almost every parameter.
Source: Strong Existence, proof of lm:orig_space, lines 1094–1103; proof of thm:Bhat-B, line 1144. -/
theorem raw_field_eq_fixed_field_of_same_positive_quantile_paths
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (q : Lattice → Environment → unitInterval → (ℕ → Lattice))
    (s₀ : unitInterval) (hs₀ : 0 < (s₀ : ℝ))
    (C : Lattice → Lattice → Environment → ℝ)
    (R : Environment × unitInterval → (Lattice → Lattice → ℝ))
    (hGeo : ∀ᵐ ω ∂environmentLaw μ, ∀ (u : Lattice) (s : unitInterval),
      IsLocallyRightmostGeodesic ω u (q u ω s))
    (hCoal₀ : ∀ᵐ ω ∂environmentLaw μ, ∀ u v : Lattice,
      paths_coalesce u v (q u ω s₀) (q v ω s₀))
    (hAllPaths : ∀ᵐ ω ∂environmentLaw μ,
      ∀ s t : unitInterval, 0 < (s : ℝ) → 0 < (t : ℝ) →
        ∀ u : Lattice, q u ω s = q u ω t)
    (hCLimit : ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
      has_passage_difference_limits ω (q u ω s₀) (fun x y => C x y ω))
    (hRLimit : ∀ᵐ a ∂(environmentLaw μ).prod (volume : Measure unitInterval),
      ∀ u : Lattice, has_passage_difference_limits a.1 (q u a.1 a.2) (R a)) :
    ∀ᵐ a ∂(environmentLaw μ).prod (volume : Measure unitInterval),
      ∀ x y : Lattice, R a x y = C x y a.1 := by
  classical
  let ν : Measure (Environment × unitInterval) :=
    (environmentLaw μ).prod (volume : Measure unitInterval)
  have hGoodω : ∀ᵐ ω ∂environmentLaw μ,
      (∀ u : Lattice, IsLocallyRightmostGeodesic ω u (q u ω s₀)) ∧
      (∀ u v : Lattice, ∃ m n : ℕ,
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
        ∀ k : ℕ, q u ω s₀ (m + k) = q v ω s₀ (n + k)) ∧
      (∀ s t : unitInterval, 0 < (s : ℝ) → 0 < (t : ℝ) →
        ∀ u : Lattice, q u ω s = q u ω t) ∧
      (∀ u x y : Lattice, ∀ N : ℕ,
        x ≤ q u ω s₀ N → y ≤ q u ω s₀ N →
        Tendsto (fun n : ℕ =>
          lastPassage ω x
            (((q u ω s₀ (N + n)).1 - x.1).toNat,
             ((q u ω s₀ (N + n)).2 - x.2).toNat) -
          lastPassage ω y
            (((q u ω s₀ (N + n)).1 - y.1).toNat,
             ((q u ω s₀ (N + n)).2 - y.2).toNat))
          atTop (𝓝 (C x y ω))) := by
    filter_upwards [hGeo, hCoal₀, hAllPaths, hCLimit]
      with ω hωGeo hωCoal hωPaths hωLimit
    exact ⟨fun u => (hωGeo u s₀), hωCoal, hωPaths, hωLimit⟩
  have hGoodωProd : ∀ᵐ a ∂ν,
      (∀ u : Lattice, IsLocallyRightmostGeodesic a.1 u (q u a.1 s₀)) ∧
      (∀ u v : Lattice, ∃ m n : ℕ,
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
        ∀ k : ℕ, q u a.1 s₀ (m + k) = q v a.1 s₀ (n + k)) ∧
      (∀ s t : unitInterval, 0 < (s : ℝ) → 0 < (t : ℝ) →
        ∀ u : Lattice, q u a.1 s = q u a.1 t) ∧
      (∀ u x y : Lattice, ∀ N : ℕ,
        x ≤ q u a.1 s₀ N → y ≤ q u a.1 s₀ N →
        Tendsto (fun n : ℕ =>
          lastPassage a.1 x
            (((q u a.1 s₀ (N + n)).1 - x.1).toNat,
             ((q u a.1 s₀ (N + n)).2 - x.2).toNat) -
          lastPassage a.1 y
            (((q u a.1 s₀ (N + n)).1 - y.1).toNat,
             ((q u a.1 s₀ (N + n)).2 - y.2).toNat))
          atTop (𝓝 (C x y a.1))) := by
    have h := ae_of_ae_map (μ := ν) (f := Prod.fst)
      measurable_fst.aemeasurable
      (by simpa only [ν, measurePreserving_fst.map_eq] using hGoodω)
    simpa only [ν] using h
  have hPositive : ∀ᵐ (s : unitInterval) ∂(volume : Measure unitInterval),
      0 < (s : ℝ) := by
    have hNotZero : ∀ᵐ (s : unitInterval) ∂(volume : Measure unitInterval),
        s ≠ (0 : unitInterval) := by
      rw [ae_iff]
      simp
    filter_upwards [hNotZero] with s hs
    have hne : (s : ℝ) ≠ 0 := fun hz => hs (Subtype.ext hz)
    exact lt_of_le_of_ne s.2.1 (Ne.symm hne)
  have hPositiveProd : ∀ᵐ a ∂ν, 0 < (a.2 : ℝ) := by
    have h := ae_of_ae_map (μ := ν) (f := Prod.snd)
      measurable_snd.aemeasurable
      (by simpa only [ν, measurePreserving_snd.map_eq] using hPositive)
    simpa only [ν] using h
  filter_upwards [hGoodωProd, hPositiveProd, hRLimit]
    with a hω hPos hRaw
  intro x y
  obtain ⟨hωGeo, hωCoal, hωPaths, hωLimit⟩ := hω
  let z : Lattice := (max x.1 y.1, max x.2 y.2)
  obtain ⟨N, M, _hLevel, hTail⟩ := hωCoal 0 z
  have hMono (u : Lattice) : Monotone (q u a.1 s₀) := by
    apply monotone_nat_of_le_succ
    intro n
    rcases (hωGeo u).2.1 n with he | hn
    · rw [he]
      constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
    · rw [hn]
      constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  have hzLower : z ≤ q z a.1 s₀ M := by
    have h := hMono z (Nat.zero_le M)
    simpa only [(hωGeo z).1] using h
  have hEntry : q 0 a.1 s₀ N = q z a.1 s₀ M := by
    simpa only [Nat.add_zero] using hTail 0
  have hxN : x ≤ q 0 a.1 s₀ N := by
    rw [hEntry]
    exact le_trans (by constructor <;> simp [z]) hzLower
  have hyN : y ≤ q 0 a.1 s₀ N := by
    rw [hEntry]
    exact le_trans (by constructor <;> simp [z]) hzLower
  have hPath : q 0 a.1 a.2 = q 0 a.1 s₀ :=
    hωPaths a.2 s₀ hPos hs₀ 0
  have hxNs : x ≤ q 0 a.1 a.2 N := by simpa only [hPath] using hxN
  have hyNs : y ≤ q 0 a.1 a.2 N := by simpa only [hPath] using hyN
  have hRawTendsto := hRaw 0 x y N hxNs hyNs
  rw [hPath] at hRawTendsto
  exact tendsto_nhds_unique hRawTendsto (hωLimit 0 x y N hxN hyN)
/-- The joint environment-field law transfers a deterministic measurable
field graph to the actual coupled cocycle.
Source: Strong Existence, proof of thm:Bhat-B, lines 1141–1145. -/
theorem actual_cocycle_eq_of_same_joint_field_law
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hBMeas : Measurable
      (fun p : (Lattice × Lattice) × ProcessSample => B p.1.1 p.1.2 p.2))
    (C : Lattice → Lattice → Environment → ℝ)
    (hCMeas : Measurable
      (fun p : (Lattice × Lattice) × Environment => C p.1.1 p.1.2 p.2))
    (R : Environment × unitInterval → (Lattice → Lattice → ℝ))
    (hRMeas : Measurable R)
    (hLaw :
      (((environmentLaw μ).prod (volume : Measure unitInterval)).map
        (fun a : Environment × unitInterval => (a.1, R a))) =
      P.map (fun b : ProcessSample =>
        (processEnvironment b, fun x y : Lattice => B x y b)))
    (hRawEq : ∀ᵐ a ∂(environmentLaw μ).prod (volume : Measure unitInterval),
      ∀ x y : Lattice, R a x y = C x y a.1) :
    ∀ᵐ b ∂P, ∀ x y : Lattice, B x y b = C x y (processEnvironment b) := by
  classical
  let Cmap : Environment → (Lattice → Lattice → ℝ) :=
    fun ω x y => C x y ω
  have hCcoord (x y : Lattice) : Measurable (C x y) := by
    exact hCMeas.comp
      ((measurable_const.prodMk measurable_const).prodMk measurable_id)
  have hCmap : Measurable Cmap := by
    apply measurable_pi_iff.mpr
    intro x
    apply measurable_pi_iff.mpr
    intro y
    exact hCcoord x y
  let Graph : Set (Environment × (Lattice → Lattice → ℝ)) :=
    {v | v.2 = Cmap v.1}
  have hGraphMeas : MeasurableSet Graph := by
    exact measurableSet_eq_fun measurable_snd (hCmap.comp measurable_fst)
  have hLeftMeas : Measurable
      (fun a : Environment × unitInterval => (a.1, R a)) :=
    measurable_fst.prodMk hRMeas
  have hRightMeas : Measurable
      (fun b : ProcessSample =>
        (processEnvironment b, fun x y : Lattice => B x y b)) := by
    have hBcoord (x y : Lattice) : Measurable (B x y) := by
      exact hBMeas.comp
        ((measurable_const.prodMk measurable_const).prodMk measurable_id)
    have hBfield : Measurable
        (fun b : ProcessSample => fun x y : Lattice => B x y b) := by
      apply measurable_pi_iff.mpr
      intro x
      apply measurable_pi_iff.mpr
      intro y
      exact hBcoord x y
    exact measurable_fst.prodMk hBfield
  have hLeftGraph : ∀ᵐ a ∂(environmentLaw μ).prod
      (volume : Measure unitInterval),
      (a.1, R a) ∈ Graph := by
    filter_upwards [hRawEq] with a ha
    change R a = Cmap a.1
    funext x y
    exact ha x y
  have hMapGraph : ∀ᵐ v ∂((environmentLaw μ).prod
      (volume : Measure unitInterval)).map
        (fun a : Environment × unitInterval => (a.1, R a)), v ∈ Graph :=
    (ae_map_iff hLeftMeas.aemeasurable hGraphMeas).mpr hLeftGraph
  rw [hLaw] at hMapGraph
  have hActualGraph :=
    (ae_map_iff hRightMeas.aemeasurable hGraphMeas).mp hMapGraph
  filter_upwards [hActualGraph] with b hb
  change (fun x y : Lattice => B x y b) =
    Cmap (processEnvironment b) at hb
  intro x y
  exact congrFun (congrFun hb x) y

/-- Fubini turns product-almost-sure coalescence of the same measurable
conditional-CDF sampler into coalescence at almost every fixed parameter.
Source: Strong Existence, lines 931–973 and 1080–1082. -/
theorem ae_parameter_coalescing_real_quantile_family
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B)
    (hCoal : HasCoalescingRightmostPaths P B)
    (q : Lattice → Environment → unitInterval → (ℕ → Lattice))
    (hqMeas : ∀ u : Lattice, Measurable
      (fun a : Environment × unitInterval => q u a.1 a.2))
    (hqCDF : ∀ᵐ ω ∂environmentLaw μ,
      ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic ω u (q u ω s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (q u ω s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (condDistrib
                (fun a : ProcessSample =>
                  rightmostCocyclePath (fun x y => B x y a) u)
                processEnvironment P) ω
                  {η : ℕ → Lattice | pathSoutheastLE η γ})) :
    ∀ᵐ s ∂(volume : Measure unitInterval),
      ∀ᵐ ω ∂environmentLaw μ,
        ∀ u v : Lattice, paths_coalesce u v (q u ω s) (q v ω s) := by
  classical
  let coalesces : Environment → unitInterval → Prop := fun ω s =>
    ∀ u v : Lattice, paths_coalesce u v (q u ω s) (q v ω s)
  have hEval (u : Lattice) (i : ℕ) :
      Measurable (fun a : Environment × unitInterval => q u a.1 a.2 i) :=
    (measurable_pi_apply i).comp (hqMeas u)
  have hPairMeas (u v : Lattice) :
      MeasurableSet {a : Environment × unitInterval |
        ∃ m n : ℕ,
          u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
          ∀ k : ℕ, q u a.1 a.2 (m + k) = q v a.1 a.2 (n + k)} := by
    simp only [Set.ofPred_exists]
    refine MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun n => ?_
    have hTail : MeasurableSet {a : Environment × unitInterval |
        ∀ k : ℕ, q u a.1 a.2 (m + k) = q v a.1 a.2 (n + k)} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun k =>
        measurableSet_eq_fun (hEval u (m + k)) (hEval v (n + k))
    by_cases hLevel : u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ)
    · simpa [hLevel] using hTail
    · simp [hLevel]
  have hCoalescesMeas :
      MeasurableSet {a : Environment × unitInterval | coalesces a.1 a.2} := by
    simp only [coalesces, paths_coalesce, Set.ofPred_forall]
    exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => hPairMeas u v
  have hCoalescesProd :
      ∀ᵐ a ∂(environmentLaw μ).prod (volume : Measure unitInterval),
        coalesces a.1 a.2 := by
    simpa only [coalesces, paths_coalesce] using
      ae_coalescing_real_rightmost_quantile_family
        μ P hMarginal B hB hCoal q hqMeas hqCDF
  have hSections := MeasureTheory.Measure.ae_ae_of_ae_prod hCoalescesProd
  simpa only [coalesces, paths_coalesce] using
    (MeasureTheory.Measure.ae_ae_comm hCoalescesMeas).mp hSections

/-- The same coalescing quantile rays calibrate their finite-limit field;
therefore they are precisely that field's canonical east-tie paths.
Source: Strong Existence, lines 1375–1383 and 1012–1038. -/
theorem ae_quantile_paths_eq_canonical_of_finite_field
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (q : Lattice → Environment → unitInterval → (ℕ → Lattice))
    (s : unitInterval)
    (hqGeo : ∀ᵐ ω ∂environmentLaw μ,
      ∀ u : Lattice, IsLocallyRightmostGeodesic ω u (q u ω s))
    (hqCoal : ∀ᵐ ω ∂environmentLaw μ,
      ∀ u v : Lattice, paths_coalesce u v (q u ω s) (q v ω s))
    (C : Lattice → Lattice → Environment → ℝ)
    (hC : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) C)
    (hLimit : ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
      has_passage_difference_limits ω (q u ω s) (fun x y => C x y ω)) :
    (∀ᵐ ω ∂environmentLaw μ,
      ∀ u : Lattice,
        rightmostCocyclePath (fun x y => C x y ω) u = q u ω s) ∧
      HasCoalescingRightmostPaths (environmentLaw μ) C := by
  classical
  obtain ⟨A, hAMeas, hAFull, hFiniteUnique⟩ :=
    exists_full_event_unique_real_cocycle_of_coalescing_geodesic_family
      μ hμ hmoment
  have hAae : ∀ᵐ ω ∂environmentLaw μ, ω ∈ A :=
    (mem_ae_iff_prob_eq_one hAMeas).mpr hAFull
  have hPathIdentity : ∀ᵐ ω ∂environmentLaw μ,
      ∀ u : Lattice,
        rightmostCocyclePath (fun x y => C x y ω) u = q u ω s := by
    filter_upwards [hAae, hqGeo, hqCoal, hC.1.2.2, hC.2.1, hLimit]
      with ω hωA hωGeo hωCoal hωAdd hωRec hωLimit
    let π : Lattice → ℕ → Lattice := fun u n => q u ω s n
    have hπGeo : ∀ u : Lattice, IsLocallyRightmostGeodesic ω u (π u) :=
      fun u => hωGeo u
    have hπMono (u : Lattice) : Monotone (π u) := by
      apply monotone_nat_of_le_succ
      intro n
      rcases (hπGeo u).2.1 n with he | hn
      · rw [he]
        constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
      · rw [hn]
        constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
    obtain ⟨F, hF, _hUnique⟩ := hFiniteUnique ω hωA π hπGeo hωCoal
    have hCF : (fun x y => C x y ω) = F := by
      funext x y
      let z : Lattice := (max x.1 y.1, max x.2 y.2)
      obtain ⟨N, M, _hLevel, hTail⟩ := hωCoal 0 z
      have hzLower : z ≤ π z M := by
        have h := hπMono z (Nat.zero_le M)
        simpa only [(hπGeo z).1] using h
      have hEntry : π 0 N = π z M := by
        simpa only [Nat.add_zero] using hTail 0
      have hxN : x ≤ π 0 N := by
        rw [hEntry]
        exact le_trans (by constructor <;> simp [z]) hzLower
      have hyN : y ≤ π 0 N := by
        rw [hEntry]
        exact le_trans (by constructor <;> simp [z]) hzLower
      exact tendsto_nhds_unique (hωLimit 0 x y N hxN hyN)
        (hF.1 0 x y N hxN hyN)
    have hπCal : ∀ (u : Lattice) (n : ℕ),
        C (π u n) (π u (n + 1)) ω = ω (π u n) := by
      intro u n
      rw [show C (π u n) (π u (n + 1)) ω =
        F (π u n) (π u (n + 1)) from congrFun
          (congrFun hCF (π u n)) (π u (n + 1))]
      exact hF.2.2.2 u n
    have hπPath :=
      rightmostCocyclePath_eq_coalescing_calibrated_locallyRightmost_family
        ω (fun x y => C x y ω) hωAdd hωRec π hπGeo hωCoal hπCal
    simpa only [π] using hπPath
  refine ⟨hPathIdentity, ?_⟩
  filter_upwards [hPathIdentity, hqCoal] with ω hPath hCoal
  intro u v
  obtain ⟨m, n, hLevel, hTail⟩ := hCoal u v
  refine ⟨m, n, hLevel, ?_⟩
  intro k
  simpa only [hPath u, hPath v] using hTail k

end LPP.Busemann
