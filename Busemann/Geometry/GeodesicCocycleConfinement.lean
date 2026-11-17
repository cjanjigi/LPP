/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.OrdinaryGeodesicClusterBounds
public import LPP_Foundations.Model.LastPassage.GradientOrder
public import Busemann.Frozen.Definitions.SupportTilt
public import Busemann.Frozen.Definitions.SupportsAt
public import Busemann.Frozen.Definitions.SupportFacesUnion
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Busemann.Geometry.StrictSupportFaceSeparation
import Busemann.Geometry.StrictDirectionSequences
import Busemann.Geometry.EndpointTranslation
import Busemann.Geometry.EndpointReach
import Mathlib.Tactic

@[expose] public section
open Filter LPPDifferentiability
open scoped NNReal Topology
namespace LPP.Busemann

/-- A cluster value of the signed-root horizontal ratio gives the corresponding
two-coordinate cluster direction of the original ray. -/
theorem normalized_ray_cluster_of_horizontal_ratio_cluster
    (u : Lattice) (γ : ℕ → Lattice) (hstart : γ 0 = u)
    (hsteps : ∀ n, γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
      γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ)))
    (z : ℝ)
    (hz : MapClusterPt z atTop
      (fun n : ℕ => (((γ n).1 - u.1 : ℤ) : ℝ) / (n : ℝ))) :
    MapClusterPt (z, 1 - z) atTop
      (fun n : ℕ => (((γ n).1 : ℝ) / (n : ℝ),
        ((γ n).2 : ℝ) / (n : ℝ))) := by
  let a : ℕ → ℝ := fun n => (((γ n).1 - u.1 : ℤ) : ℝ) / (n : ℝ)
  obtain ⟨φ, hconv, hφTop⟩ := MapClusterPt.exists_seq_tendsto hz
  have hsum : ∀ n, (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) := by
    intro n
    induction n with
    | zero => simp [hstart]
    | succ n ih =>
      rcases hsteps n with he | hn
      · simp only [he, Prod.fst_add, Prod.snd_add, Nat.cast_succ]
        omega
      · simp only [hn, Prod.fst_add, Prod.snd_add, Nat.cast_succ]
        omega
  have hroot₁ : Tendsto (fun n : ℕ => (u.1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hrootSum : Tendsto
      (fun n : ℕ => ((u.1 + u.2 : ℤ) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hfirst : Tendsto
      (fun k : ℕ => ((γ (φ k)).1 : ℝ) / (φ k : ℝ)) atTop (𝓝 z) := by
    have h := hconv.add (hroot₁.comp hφTop)
    have heq (k : ℕ) :
        ((γ (φ k)).1 : ℝ) / (φ k : ℝ) =
          a (φ k) + (u.1 : ℝ) / (φ k : ℝ) := by
      dsimp only [a]
      rw [Int.cast_sub, sub_div, sub_add_cancel]
    simpa only [Function.comp_def, heq, add_zero] using h
  have hsecond : Tendsto
      (fun k : ℕ => ((γ (φ k)).2 : ℝ) / (φ k : ℝ)) atTop (𝓝 (1 - z)) := by
    have hbase : Tendsto (fun k : ℕ =>
        1 - a (φ k) + ((u.1 + u.2 : ℤ) : ℝ) / (φ k : ℝ) -
          (u.1 : ℝ) / (φ k : ℝ)) atTop (𝓝 (1 - z)) := by
      have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hconv).add
        (hrootSum.comp hφTop)).sub (hroot₁.comp hφTop)
      simpa only [Function.comp_def, sub_zero, add_zero] using h
    have heq : ∀ᶠ k : ℕ in atTop,
        ((γ (φ k)).2 : ℝ) / (φ k : ℝ) =
          1 - a (φ k) + ((u.1 + u.2 : ℤ) : ℝ) / (φ k : ℝ) -
            (u.1 : ℝ) / (φ k : ℝ) := by
      filter_upwards [hφTop.eventually (eventually_gt_atTop (0 : ℕ))] with k hk
      have hk0 : (φ k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
      have hs : ((γ (φ k)).1 : ℝ) + ((γ (φ k)).2 : ℝ) =
          ((u.1 + u.2 : ℤ) : ℝ) + (φ k : ℝ) := by
        exact_mod_cast hsum (φ k)
      dsimp only [a]
      rw [Int.cast_sub]
      field_simp [hk0]
      linarith only [hs]
    exact hbase.congr' (heq.mono fun _ h => h.symm)
  have hpair : Tendsto (fun k : ℕ =>
      (((γ (φ k)).1 : ℝ) / (φ k : ℝ),
        ((γ (φ k)).2 : ℝ) / (φ k : ℝ))) atTop (𝓝 (z, 1 - z)) :=
    hfirst.prodMk_nhds hsecond
  exact MapClusterPt.of_comp hφTop hpair.mapClusterPt

/-- Dense differentiability directions supply two calibrated faces strictly
outside the whole two-face interval of a given interior direction. The
threshold argument also handles an adjacent flat at either endpoint. -/
theorem exists_dense_barriers_outside_entire_face_interval
    (g : Quadrant → ℝ) (hcont : Continuous g)
    (hconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (D : ℕ → InteriorDirection) (hDense : DenseRange D)
    (hL hR : InteriorDirection → SupportTilt g)
    (left right : InteriorDirection → InteriorDirection)
    (hExtreme : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1)
    (hEndpoints : ∀ ξ : InteriorDirection,
      left ξ ∈ supportFacesUnion g (hL ξ) (hR ξ) ∧
      right ξ ∈ supportFacesUnion g (hL ξ) (hR ξ) ∧
      ∀ η : InteriorDirection,
        η ∈ supportFacesUnion g (hL ξ) (hR ξ) ↔
          (left ξ).1.1 ≤ η.1.1 ∧ η.1.1 ≤ (right ξ).1.1)
    (hSingle : ∀ n, hL (D n) = hR (D n))
    (hGaps : ∀ n, g (1, 0) < -(hL (D n)).1.1 ∧
      g (0, 1) < -(hL (D n)).1.2)
    (ξ : InteriorDirection) :
    ∃ kNW kSE : ℕ,
      ((right (D kNW)).1.1 : ℝ) < ((left ξ).1.1 : ℝ) ∧
      ((right ξ).1.1 : ℝ) < ((left (D kSE)).1.1 : ℝ) := by
  let qNW := left ξ
  let qSE := right ξ
  obtain ⟨furtherNW, _, hFurtherNW, _, _⟩ :=
    exists_strict_left_right_direction_sequences (left qNW)
  obtain ⟨_, furtherSE, hFurtherSE, _, _⟩ :=
    exists_strict_left_right_direction_sequences (right qSE)
  have hCoord : Continuous (fun ζ : InteriorDirection => (ζ.1.1 : ℝ)) := by fun_prop
  have hOpenNW : IsOpen {ζ : InteriorDirection | (ζ.1.1 : ℝ) < ((left qNW).1.1 : ℝ)} :=
    isOpen_Iio.preimage hCoord
  have hOpenSE : IsOpen {ζ : InteriorDirection | ((right qSE).1.1 : ℝ) < (ζ.1.1 : ℝ)} :=
    isOpen_Ioi.preimage hCoord
  obtain ⟨kNW, hkNW⟩ := hDense.exists_mem_open hOpenNW
    ⟨furtherNW 0, by exact_mod_cast (hFurtherNW 0).1⟩
  obtain ⟨kSE, hkSE⟩ := hDense.exists_mem_open hOpenSE
    ⟨furtherSE 0, by exact_mod_cast (hFurtherSE 0).2⟩
  have hNWface (ζ : InteriorDirection) (hζ : ζ ∈ supportFace g (hL qNW)) :
      (left qNW).1.1 ≤ ζ.1.1 :=
    ((hEndpoints qNW).2.2 ζ).mp (Or.inl hζ) |>.1
  have hSEface (ζ : InteriorDirection) (hζ : ζ ∈ supportFace g (hR qSE)) :
      ζ.1.1 ≤ (right qSE).1.1 :=
    ((hEndpoints qSE).2.2 ζ).mp (Or.inr hζ) |>.2
  obtain ⟨θNW, _, _, hθNW, hAllNW⟩ :=
    exists_strict_threshold_left_of_minimal_support_face
      g hcont hconc hhom qNW (left qNW) (D kNW)
      (hL qNW) (hL (D kNW)) (hExtreme qNW).1
      (fun k hk => ((hExtreme qNW).2.2 k hk).1)
      hNWface (hExtreme (D kNW)).1 hkNW (hGaps kNW).1 (hGaps kNW).2
  obtain ⟨θSE, _, _, hθSE, hAllSE⟩ :=
    exists_strict_threshold_right_of_maximal_support_face
      g hcont hconc hhom qSE (right qSE) (D kSE)
      (hR qSE) (hL (D kSE)) (hExtreme qSE).2.1
      (fun k hk => ((hExtreme qSE).2.2 k hk).2)
      hSEface (hExtreme (D kSE)).1 hkSE (hGaps kSE).1 (hGaps kSE).2
  have hRightMem : right (D kNW) ∈ supportFace g (hL (D kNW)) := by
    have h := (hEndpoints (D kNW)).2.1
    rw [← hSingle kNW, supportFacesUnion, Set.union_self] at h
    exact h
  have hLeftMem : left (D kSE) ∈ supportFace g (hL (D kSE)) := by
    have h := (hEndpoints (D kSE)).1
    rw [← hSingle kSE, supportFacesUnion, Set.union_self] at h
    exact h
  have hθNW' : θNW < ((left ξ).1.1 : ℝ) := by simpa only [qNW] using hθNW
  have hθSE' : ((right ξ).1.1 : ℝ) < θSE := by simpa only [qSE] using hθSE
  exact ⟨kNW, kSE,
    (hAllNW _ hRightMem).trans hθNW',
    hθSE'.trans (hAllSE _ hLeftMem)⟩


/-- A compactly directed ordinary ray eventually lies strictly between two
calibrated barrier ratios whose entire faces are separated from its cluster
interval. The bounds apply to all cluster points, including adjacent flats. -/
theorem eventually_between_separated_barrier_ratios
    (a nw se : ℕ → ℝ) (L R l r : ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1)
    (hnw : ∀ n, 0 ≤ nw n ∧ nw n ≤ 1)
    (hse : ∀ n, 0 ≤ se n ∧ se n ≤ 1)
    (hcluster : ∀ z : ℝ, MapClusterPt z atTop a → L ≤ z ∧ z ≤ R)
    (hNW : limsup nw atTop ≤ l) (hLeft : l < L)
    (hRight : R < r) (hSE : r ≤ liminf se atTop) :
    ∀ᶠ n : ℕ in atTop, nw n < a n ∧ a n < se n := by
  have boundedBelow (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 1) :
      (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) f :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun n => (hf n).1)
  have boundedAbove (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 1) :
      (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) f :=
    isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall fun n => (hf n).2)
  have hLiminf : L ≤ liminf a atTop :=
    (hcluster _ (MapClusterPt.liminf
      (boundedAbove a ha).isCoboundedUnder_ge (boundedBelow a ha))).1
  have hLimsup : limsup a atTop ≤ R :=
    (hcluster _ (MapClusterPt.limsup
      (boundedBelow a ha).isCoboundedUnder_le (boundedAbove a ha))).2
  let cL : ℝ := (l + L) / 2
  let cR : ℝ := (R + r) / 2
  have hNWsmall : ∀ᶠ n : ℕ in atTop, nw n < cL :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hNW (by dsimp [cL]; linarith))
      (boundedAbove nw hnw)
  have hALarge : ∀ᶠ n : ℕ in atTop, cL < a n :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le (by dsimp [cL]; linarith) hLiminf)
      (boundedBelow a ha)
  have hASmall : ∀ᶠ n : ℕ in atTop, a n < cR :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hLimsup (by dsimp [cR]; linarith))
      (boundedAbove a ha)
  have hSElarge : ∀ᶠ n : ℕ in atTop, cR < se n :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le (by dsimp [cR]; linarith) hSE)
      (boundedBelow se hse)
  filter_upwards [hNWsmall, hALarge, hASmall, hSElarge] with n h1 h2 h3 h4
  exact ⟨h1.trans h2, h3.trans h4⟩

/-- Two rays with the same signed root and unit up-right steps have endpoints
at the same absolute level when evaluated at the same local time. -/
theorem same_level_of_same_root_up_right_steps
    (u : Lattice) (γ ρ : ℕ → Lattice)
    (hγ0 : γ 0 = u) (hρ0 : ρ 0 = u)
    (hγ : ∀ n, γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
      γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ)))
    (hρ : ∀ n, ρ (n + 1) = ρ n + ((1 : ℤ), (0 : ℤ)) ∨
      ρ (n + 1) = ρ n + ((0 : ℤ), (1 : ℤ)))
    (n : ℕ) : (γ n).1 + (γ n).2 = (ρ n).1 + (ρ n).2 := by
  have level (q : ℕ → Lattice) (hq0 : q 0 = u)
      (hq : ∀ n, q (n + 1) = q n + ((1 : ℤ), (0 : ℤ)) ∨
        q (n + 1) = q n + ((0 : ℤ), (1 : ℤ))) :
      ∀ n, (q n).1 + (q n).2 = u.1 + u.2 + (n : ℤ) := by
    intro k
    induction k with
    | zero => simp [hq0]
    | succ k ih =>
      rcases hq k with h | h <;>
        simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega
  rw [level γ hγ0 hγ n, level ρ hρ0 hρ n]

/-- An interior face barrier eventually lies in a rational interior cone even
when passage is measured from an arbitrary signed start. Both neighboring
starts eventually reach its actual endpoint. This is the domain and cone
translation used in Strong Existence, g602 and g619, lines 1663–1693. -/
theorem eventually_signed_start_cone_of_face_barrier
    (u x : Lattice) (d : ℕ → ℕ × ℕ)
    (left right : InteriorDirection)
    (hface : approachesFaceInterval d left right) :
    ∃ ε : ℚ, 0 < ε ∧ ε < 1 / 2 ∧
      ∀ᶠ n : ℕ in atTop,
        let v : Lattice := u + (((d n).1 : ℤ), ((d n).2 : ℤ))
        let D : ℕ × ℕ := ((v.1 - x.1).toNat, (v.2 - x.2).toNat)
        x ≤ v ∧ x + ((1 : ℤ), (0 : ℤ)) ≤ v ∧
          x + ((0 : ℤ), (1 : ℤ)) ≤ v ∧
          (ε : ℝ) ≤ (D.1 : ℝ) / ((D.1 + D.2 : ℕ) : ℝ) ∧
          (D.1 : ℝ) / ((D.1 + D.2 : ℕ) : ℝ) ≤ 1 - (ε : ℝ) := by
  let z : Lattice := x - u
  let q (n : ℕ) : ℝ := ((d n).1 : ℝ) / (((d n).1 + (d n).2 : ℕ) : ℝ)
  let D (n : ℕ) : ℕ × ℕ :=
    ((((d n).1 : ℤ) - z.1).toNat, (((d n).2 : ℤ) - z.2).toNat)
  let r (n : ℕ) : ℝ := (D n).1 / (((D n).1 + (D n).2 : ℕ) : ℝ)
  have hshift :=
    approachesFaceInterval_translated_displacement_asymptotics d left right hface z
  have herr : Tendsto (fun n => r n - q n) atTop (𝓝 0) := by
    simpa only [D, r, q] using hshift.2
  have hqBounds (n : ℕ) : 0 ≤ q n ∧ q n ≤ 1 := by
    by_cases hz : (d n).1 + (d n).2 = 0
    · have hfirst : (d n).1 = 0 := by omega
      simp [q, hfirst]
    · have hpos : (0 : ℝ) < (((d n).1 + (d n).2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) hpos.le
      · apply (div_le_iff₀ hpos).2
        simpa only [one_mul] using
          (show ((d n).1 : ℝ) ≤ (((d n).1 + (d n).2 : ℕ) : ℝ) by
            exact_mod_cast Nat.le_add_right (d n).1 (d n).2)
  have hBelow : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) q :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun n => (hqBounds n).1)
  have hAbove : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) q :=
    isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall fun n => (hqBounds n).2)
  have hleftPos : (0 : ℝ) < (left.1.1 : ℝ) := by exact_mod_cast left.2.1
  have hrightLt : (right.1.1 : ℝ) < 1 := by
    have hs := right.2.2.2
    have hp : (0 : ℝ) < (right.1.2 : ℝ) := by exact_mod_cast right.2.2.1
    linarith
  let a : ℝ := (left.1.1 : ℝ) / 2
  let b : ℝ := ((right.1.1 : ℝ) + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : b < 1 := by dsimp [b]; linarith
  obtain ⟨ε, hεPos, hεSmall⟩ :=
    exists_rat_btwn (show (0 : ℝ) < min (a / 2) (min ((1 - b) / 2) (1 / 2)) by
      apply lt_min (by linarith) (lt_min (by linarith) (by norm_num)))
  have hεa : (ε : ℝ) < a / 2 := lt_of_lt_of_le hεSmall (min_le_left _ _)
  have hεb : (ε : ℝ) < (1 - b) / 2 :=
    lt_of_lt_of_le hεSmall (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεHalf : (ε : ℝ) < 1 / 2 :=
    lt_of_lt_of_le hεSmall (le_trans (min_le_right _ _) (min_le_right _ _))
  have hqLow : ∀ᶠ n : ℕ in atTop, a < q n :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le (by dsimp [a]; linarith) hface.2.1)
      hBelow
  have hqHigh : ∀ᶠ n : ℕ in atTop, q n < b :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hface.2.2 (by dsimp [b]; linarith))
      hAbove
  have herrLow : ∀ᶠ n : ℕ in atTop, -(ε : ℝ) < r n - q n :=
    (tendsto_order.1 herr).1 _ (by linarith)
  have herrHigh : ∀ᶠ n : ℕ in atTop, r n - q n < (ε : ℝ) :=
    (tendsto_order.1 herr).2 _ (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_reaches_of_approachesFaceInterval
    d left right hface z (0 : Fin 2)
  obtain ⟨N₂, hN₂⟩ := eventually_reaches_of_approachesFaceInterval
    d left right hface z (1 : Fin 2)
  have hReach : ∀ᶠ n : ℕ in atTop,
      z ≤ latticeEndpoint (d n) ∧
      z + ((1 : ℤ), (0 : ℤ)) ≤ latticeEndpoint (d n) ∧
      z + ((0 : ℤ), (1 : ℤ)) ≤ latticeEndpoint (d n) := by
    filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop N₂] with n hn₁ hn₂
    have h₁ := hN₁ n hn₁
    have h₂ := hN₂ n hn₂
    simpa only [finiteEdgeStep, latticeEndpoint] using ⟨h₁.1, h₁.2, h₂.2⟩
  have hεHalfQ : ε < (1 / 2 : ℚ) := by
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa using hεHalf
  refine ⟨ε, by exact_mod_cast hεPos, hεHalfQ, ?_⟩
  filter_upwards [hqLow, hqHigh, herrLow, herrHigh, hReach] with n hlow hhigh heLow heHigh hreach
  have hactual :
      let v : Lattice := u + (((d n).1 : ℤ), ((d n).2 : ℤ))
      let D₀ : ℕ × ℕ := ((v.1 - x.1).toNat, (v.2 - x.2).toNat)
      D₀ = D n := by
    dsimp only [D, z]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
      <;> congr 1 <;> omega
  have hvalid :
      let v : Lattice := u + (((d n).1 : ℤ), ((d n).2 : ℤ))
      x ≤ v ∧ x + ((1 : ℤ), (0 : ℤ)) ≤ v ∧
        x + ((0 : ℤ), (1 : ℤ)) ≤ v := by
    simp only [z, latticeEndpoint, Prod.le_def,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hreach ⊢
    omega
  have hratioEq :
      let v : Lattice := u + (((d n).1 : ℤ), ((d n).2 : ℤ))
      let D₀ : ℕ × ℕ := ((v.1 - x.1).toNat, (v.2 - x.2).toNat)
      (D₀.1 : ℝ) / ((D₀.1 + D₀.2 : ℕ) : ℝ) = r n := by
    exact congrArg
      (fun e : ℕ × ℕ => (e.1 : ℝ) / ((e.1 + e.2 : ℕ) : ℝ)) hactual
  dsimp only
  rw [hratioEq]
  exact ⟨hvalid.1, hvalid.2.1, hvalid.2.2, by dsimp [r] at *; linarith,
    by dsimp [r] at *; linarith⟩

/-- The original-law uniform neighbor event bounds both increments at an
interior barrier endpoint, from any signed start. Strong Existence, g602 and
g609, lines 1663–1693. -/
theorem eventually_signed_barrier_neighbor_upper_bounds
    (ω : Environment)
    (hUniform : ∀ x : Lattice, ∀ ε : ℚ,
      0 < ε → ε < 1 / 2 →
      ∃ C N : ℕ, 0 < N ∧
        ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          (ε : ℝ) ≤ (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) →
          (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) ≤ 1 - (ε : ℝ) →
          0 < d.1 ∧ 0 < d.2 ∧
          |lastPassage ω x d -
            lastPassage ω (x + ((1 : ℤ), (0 : ℤ))) (d.1 - 1, d.2)| ≤ (C : ℝ) ∧
          |lastPassage ω x d -
            lastPassage ω (x + ((0 : ℤ), (1 : ℤ))) (d.1, d.2 - 1)| ≤ (C : ℝ))
    (u x : Lattice) (d : ℕ → ℕ × ℕ)
    (left right : InteriorDirection)
    (hface : approachesFaceInterval d left right) :
    ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
      let v : Lattice := u + (((d n).1 : ℤ), ((d n).2 : ℤ))
      x ≤ v ∧ x + ((1 : ℤ), (0 : ℤ)) ≤ v ∧
        x + ((0 : ℤ), (1 : ℤ)) ≤ v ∧
        lastPassage ω x ((v.1 - x.1).toNat, (v.2 - x.2).toNat) -
          lastPassage ω (x + ((1 : ℤ), (0 : ℤ)))
            ((v.1 - (x + ((1 : ℤ), (0 : ℤ))).1).toNat,
             (v.2 - (x + ((1 : ℤ), (0 : ℤ))).2).toNat) ≤ K ∧
        lastPassage ω x ((v.1 - x.1).toNat, (v.2 - x.2).toNat) -
          lastPassage ω (x + ((0 : ℤ), (1 : ℤ)))
            ((v.1 - (x + ((0 : ℤ), (1 : ℤ))).1).toNat,
             (v.2 - (x + ((0 : ℤ), (1 : ℤ))).2).toNat) ≤ K := by
  obtain ⟨ε, hεPos, hεHalf, hCone⟩ :=
    eventually_signed_start_cone_of_face_barrier u x d left right hface
  obtain ⟨C, N, _hNpos, hBound⟩ := hUniform x ε hεPos hεHalf
  let z : Lattice := x - u
  let d' (n : ℕ) : ℕ × ℕ :=
    ((((d n).1 : ℤ) - z.1).toNat, (((d n).2 : ℤ) - z.2).toNat)
  have hsize : Tendsto (fun n => (d' n).1 + (d' n).2) atTop atTop := by
    simpa only [d', z] using
      (approachesFaceInterval_translated_displacement_asymptotics
        d left right hface z).1
  have hsizeEvent : ∀ᶠ n : ℕ in atTop, N ≤ (d' n).1 + (d' n).2 :=
    tendsto_atTop.1 hsize N
  refine ⟨(C : ℝ), ?_⟩
  filter_upwards [hCone, hsizeEvent] with n hcone hnSize
  let v : Lattice := u + (((d n).1 : ℤ), ((d n).2 : ℤ))
  let D₀ : ℕ × ℕ := ((v.1 - x.1).toNat, (v.2 - x.2).toNat)
  have hD : D₀ = d' n := by
    apply Prod.ext <;> simp only [D₀, d', z, v, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> congr 1 <;> omega
  have hN : N ≤ D₀.1 + D₀.2 := by rw [hD]; exact hnSize
  have hValue := hBound D₀ hN hcone.2.2.2.1 hcone.2.2.2.2
  have hEastReach : x.1 + 1 ≤ v.1 := by
    simpa only [v, Prod.fst_add] using hcone.2.1.1
  have hSouthReach : x.2 + 1 ≤ v.2 := by
    simpa only [v, Prod.snd_add] using hcone.2.2.1.2
  have hEastD :
      ((v.1 - (x + ((1 : ℤ), (0 : ℤ))).1).toNat,
       (v.2 - (x + ((1 : ℤ), (0 : ℤ))).2).toNat) =
        (D₀.1 - 1, D₀.2) := by
    apply Prod.ext <;> dsimp [D₀] <;> omega
  have hSouthD :
      ((v.1 - (x + ((0 : ℤ), (1 : ℤ))).1).toNat,
       (v.2 - (x + ((0 : ℤ), (1 : ℤ))).2).toNat) =
        (D₀.1, D₀.2 - 1) := by
    apply Prod.ext <;> dsimp [D₀] <;> omega
  dsimp only [v, D₀] at hcone ⊢
  refine ⟨hcone.1, hcone.2.1, hcone.2.2.1, ?_, ?_⟩
  · rw [hEastD]
    exact (le_abs_self _).trans hValue.2.2.1
  · rw [hSouthD]
    exact (le_abs_self _).trans hValue.2.2.2

end LPP.Busemann
