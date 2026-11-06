/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.WeakNegativeShape
public import LPP_Foundations.Analysis.HomogeneousShapeLipschitz
public import Differentiability.Model.Paths.DefectAlgebra
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Sublinear geodesic defect along the floor endpoints

The geodesic defect along the floor endpoints is sublinear in n. The proof splits
the error into a bounded deterministic part and the sampling error of the shape.
Path weights exclude the terminal vertex.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- The floor endpoint on level n, its transverse coordinate and its distance
from n times the direction. This includes the zero endpoint. -/
theorem floor_direction_endpoint_geometry (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    let k : ℕ := ⌊(n : ℝ) * a⌋₊
    let d : ℕ × ℕ := (k, n - k)
    d.1 + d.2 = n ∧
      -1 < (1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ) ∧
      (1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ) ≤ 0 ∧
      |(d.1 : ℝ) - (n : ℝ) * a| +
        |(d.2 : ℝ) - (n : ℝ) * (1 - a)| ≤ 2 := by
  dsimp only
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hna : 0 ≤ (n : ℝ) * a := mul_nonneg hn ha0.le
  have hkn : ⌊(n : ℝ) * a⌋₊ ≤ n :=
    Nat.floor_le_of_le (by nlinarith)
  have hcast : ((n - ⌊(n : ℝ) * a⌋₊ : ℕ) : ℝ) =
      (n : ℝ) - (⌊(n : ℝ) * a⌋₊ : ℝ) := Nat.cast_sub hkn
  have hfloor := Nat.floor_le hna
  have hfloor' := Nat.lt_floor_add_one ((n : ℝ) * a)
  have hrho : (1 - a) * (⌊(n : ℝ) * a⌋₊ : ℝ) -
      a * ((n - ⌊(n : ℝ) * a⌋₊ : ℕ) : ℝ) =
      (⌊(n : ℝ) * a⌋₊ : ℝ) - (n : ℝ) * a := by rw [hcast]; ring
  refine ⟨Nat.add_sub_of_le hkn, ?_, ?_, ?_⟩
  · rw [hrho]; linarith
  · rw [hrho]; linarith
  · rw [hcast]
    have hfirst : |(⌊(n : ℝ) * a⌋₊ : ℝ) - (n : ℝ) * a| ≤ 1 :=
      Nat.abs_floor_sub_le hna
    have hsecond : (n : ℝ) - (⌊(n : ℝ) * a⌋₊ : ℝ) - (n : ℝ) * (1 - a) =
        -((⌊(n : ℝ) * a⌋₊ : ℝ) - (n : ℝ) * a) := by ring
    rw [hsecond, abs_neg]
    linarith

/-- The average of the two supports at the floor endpoint has the advertised slope
and bounded floor error. No differentiability or corner premise is needed. -/
theorem floor_direction_average_support_bound (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (G dl dr : ℝ) (n : ℕ) :
    let d : ℕ × ℕ := (⌊(n : ℝ) * a⌋₊, n - ⌊(n : ℝ) * a⌋₊)
    let rho : ℝ := (1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)
    let fm : ℝ := G * ((d.1 : ℝ) + (d.2 : ℝ)) + dl * rho
    let fp : ℝ := G * ((d.1 : ℝ) + (d.2 : ℝ)) + dr * rho
    (fm + fp) / 2 = (n : ℝ) * G + ((dl + dr) / 2) * rho ∧
      |(fm + fp) / 2 - (n : ℝ) * G| ≤ |(dl + dr) / 2| := by
  let d : ℕ × ℕ := (⌊(n : ℝ) * a⌋₊, n - ⌊(n : ℝ) * a⌋₊)
  have hgeom := floor_direction_endpoint_geometry a ha0 ha1 n
  change d.1 + d.2 = n ∧ _ at hgeom
  have hlevel : (d.1 : ℝ) + (d.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast hgeom.1
  dsimp only
  change _ = _ ∧ _ ≤ _
  have halg : (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
      dl * ((1-a)*(d.1:ℝ)-a*(d.2:ℝ)) +
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
      dr * ((1-a)*(d.1:ℝ)-a*(d.2:ℝ)))) / 2 =
      (n : ℝ)*G + ((dl+dr)/2)*((1-a)*(d.1:ℝ)-a*(d.2:ℝ)) := by
    rw [hlevel]; ring
  constructor
  · exact halg
  · rw [halg]
    rw [add_sub_cancel_left, abs_mul]
    have hrho : |(1-a)*(d.1:ℝ)-a*(d.2:ℝ)| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hgeom.2.1], by linarith [hgeom.2.2.1]⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hrho (abs_nonneg ((dl+dr)/2))


/-- The bounded shape error at the floor endpoint. The cone Lipschitz constant
is obtained inside the proof, with cutoff 2/min(a,1-a). -/
theorem floor_direction_shape_error_bounded
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ n : ℕ, 2 / min a (1 - a) ≤ (n : ℝ) →
      let d : ℕ × ℕ := (⌊(n : ℝ) * a⌋₊, n - ⌊(n : ℝ) * a⌋₊)
      |g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) -
        (n : ℝ) * quadrantExtension g (a, 1 - a)| ≤ 2 * L := by
  let theta0 : ℝ := min a (1 - a)
  have ht0 : 0 < theta0 := lt_min ha0 (by linarith)
  have hta : theta0 ≤ a := min_le_left _ _
  have htb : theta0 ≤ 1 - a := min_le_right _ _
  have ht1 : theta0 / 2 < 1 / 2 := by dsimp [theta0]; linarith [min_le_left a (1-a)]
  obtain ⟨L, hL, hLip⟩ := quadrant_homogeneous_shape_lipschitz_on_fraction_cone
    g hgcont hgconc hhom (theta0 / 2) (by positivity) ht1
  refine ⟨L, hL, ?_⟩
  intro n hn
  let d : ℕ × ℕ := (⌊(n : ℝ) * a⌋₊, n - ⌊(n : ℝ) * a⌋₊)
  let z : Quadrant := ((d.1 : ℝ≥0), (d.2 : ℝ≥0))
  let xi : Quadrant := (⟨a, ha0.le⟩, ⟨1 - a, by linarith⟩)
  let w : Quadrant := (n : ℝ≥0) • xi
  change |g z - (n : ℝ) * quadrantExtension g (a, 1-a)| ≤ 2 * L
  have hgeom := floor_direction_endpoint_geometry a ha0 ha1 n
  change d.1 + d.2 = n ∧ _ at hgeom
  have hlevel : (d.1 : ℝ) + (d.2 : ℝ) = (n : ℝ) := by exact_mod_cast hgeom.1
  have hzn : (z.1 : ℝ) + (z.2 : ℝ) = (n : ℝ) := by exact hlevel
  have hw1 : (w.1 : ℝ) = (n : ℝ) * a := by rfl
  have hw2 : (w.2 : ℝ) = (n : ℝ) * (1-a) := by rfl
  have hwn : (w.1 : ℝ) + (w.2 : ℝ) = (n : ℝ) := by rw [hw1, hw2]; ring
  have hlarge : 2 ≤ theta0 * (n : ℝ) := by
    have h := (div_le_iff₀ ht0).mp hn
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hza : (n : ℝ)*a - 1 ≤ (d.1 : ℝ) := by
    have hr := hgeom.2.1
    rw [← hlevel] at hr
    nlinarith
  have hzb : (n : ℝ)*(1-a) ≤ (d.2 : ℝ) := by
    have hr := hgeom.2.2.1
    nlinarith [hlevel]
  have hprodA : theta0 * (n : ℝ) ≤ a * (n : ℝ) := mul_le_mul_of_nonneg_right hta hn0
  have hprodB : theta0 * (n : ℝ) ≤ (1-a) * (n : ℝ) := mul_le_mul_of_nonneg_right htb hn0
  have hcone : (theta0/2)*((z.1:ℝ)+(z.2:ℝ)) ≤ (z.1:ℝ) ∧
      (theta0/2)*((z.1:ℝ)+(z.2:ℝ)) ≤ (z.2:ℝ) ∧
      (theta0/2)*((w.1:ℝ)+(w.2:ℝ)) ≤ (w.1:ℝ) ∧
      (theta0/2)*((w.1:ℝ)+(w.2:ℝ)) ≤ (w.2:ℝ) := by
    rw [hzn, hwn, hw1, hw2]
    change (theta0/2)*(n:ℝ) ≤ (d.1:ℝ) ∧
      (theta0/2)*(n:ℝ) ≤ (d.2:ℝ) ∧ _
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  have hbound := hLip z w hcone
  have hdist : |(z.1:ℝ)-(w.1:ℝ)| + |(z.2:ℝ)-(w.2:ℝ)| ≤ 2 := by
    rw [hw1, hw2]
    exact hgeom.2.2.2
  have hxi : g xi = quadrantExtension g (a,1-a) := by
    symm
    exact quadrantExtension_quadrantInclusion g xi
  have hgw : g w = (n : ℝ) * quadrantExtension g (a,1-a) := by
    exact (hhom (n : ℝ≥0) xi).trans (congrArg ((n : ℝ) * ·) hxi)
  rw [← hgw]
  calc
    |g z - g w| ≤ L * (|(z.1:ℝ)-(w.1:ℝ)| + |(z.2:ℝ)-(w.2:ℝ)|) := hbound
    _ ≤ L * 2 := mul_le_mul_of_nonneg_left hdist (by linarith)
    _ = 2 * L := by ring


/-- On the uniform origin shape event the normalized maximum defect vanishes.
The deterministic part is bounded using the cone estimate for the quadrant shape. -/
theorem floor_direction_geodesic_defect_tendsto
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (ω : Environment)
    (hshape : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
      ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a+h,1-a-h)
    let dl : ℝ := derivWithin H (Iio 0) 0
    let dr : ℝ := derivWithin H (Ioi 0) 0
    let favg : ℕ × ℕ → ℝ := fun d =>
      H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + ((dl+dr)/2) *
        ((1-a)*(d.1:ℝ)-a*(d.2:ℝ))
    Tendsto (fun n : ℕ =>
      let d : ℕ × ℕ := (⌊(n : ℝ)*a⌋₊,n-⌊(n : ℝ)*a⌋₊)
      (favg d - lastPassage ω 0 d) / (n : ℝ)) atTop (𝓝 0) := by
  let H : ℝ → ℝ := fun h => quadrantExtension g (a+h,1-a-h)
  let dl : ℝ := derivWithin H (Iio 0) 0
  let dr : ℝ := derivWithin H (Ioi 0) 0
  let slope : ℝ := (dl+dr)/2
  let favg : ℕ × ℕ → ℝ := fun d =>
    H 0 * ((d.1 : ℝ)+(d.2 : ℝ)) + slope*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))
  change Tendsto (fun n : ℕ =>
    let d : ℕ × ℕ := (⌊(n : ℝ)*a⌋₊,n-⌊(n : ℝ)*a⌋₊)
    (favg d - lastPassage ω 0 d) / (n : ℝ)) atTop (𝓝 0)
  obtain ⟨L,hL,hbound⟩ := floor_direction_shape_error_bounded g hgcont hgconc hhom a ha0 ha1
  let C : ℝ := |slope| + 2*L
  have hC : 0 ≤ C := by dsimp [C]; linarith [abs_nonneg slope]
  have hHzero : H 0 = quadrantExtension g (a,1-a) := by simp only [H,add_zero,sub_zero]
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hεhalf : 0 < ε/2 := by positivity
  obtain ⟨Ns,hNs,hs⟩ := hshape (ε/2) hεhalf
  obtain ⟨Nc,hc⟩ := Metric.tendsto_atTop.1
    (tendsto_const_div_atTop_nhds_zero_nat C) (ε/2) hεhalf
  obtain ⟨Nb,hNb⟩ := exists_nat_ge (2 / min a (1-a))
  refine ⟨max Ns (max Nc (max Nb 1)), ?_⟩
  intro n hn
  have hns : Ns ≤ n := (le_max_left _ _).trans hn
  have hnc : Nc ≤ n := (le_max_left Nc (max Nb 1)).trans ((le_max_right _ _).trans hn)
  have hnb : Nb ≤ n := (le_max_left Nb 1).trans
    ((le_max_right Nc (max Nb 1)).trans ((le_max_right _ _).trans hn))
  have hn1 : 1 ≤ n := (le_max_right Nb 1).trans
    ((le_max_right Nc (max Nb 1)).trans ((le_max_right _ _).trans hn))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  let d : ℕ × ℕ := (⌊(n : ℝ)*a⌋₊,n-⌊(n : ℝ)*a⌋₊)
  let z : Quadrant := ((d.1:ℝ≥0),(d.2:ℝ≥0))
  have hgeom := floor_direction_endpoint_geometry a ha0 ha1 n
  change d.1+d.2=n ∧ _ at hgeom
  have hlevel : (d.1:ℝ)+(d.2:ℝ)=(n:ℝ) := by exact_mod_cast hgeom.1
  have hsupport : |favg d - (n:ℝ)*H 0| ≤ |slope| := by
    have hh := (floor_direction_average_support_bound a ha0 ha1 (H 0) dl dr n).2
    have halg : (H 0*((d.1:ℝ)+(d.2:ℝ))+dl*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))+
        (H 0*((d.1:ℝ)+(d.2:ℝ))+dr*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))))/2 = favg d := by
      dsimp [favg,slope]; ring
    change |(H 0*((d.1:ℝ)+(d.2:ℝ))+dl*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))+
        (H 0*((d.1:ℝ)+(d.2:ℝ))+dr*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))))/2-(n:ℝ)*H 0| ≤ |slope| at hh
    rw [halg] at hh
    exact hh
  have hshapeBound : |g z - (n:ℝ)*H 0| ≤ 2*L := by
    rw [hHzero]
    exact hbound n (hNb.trans (by exact_mod_cast hnb))
  have hdet : |favg d - g z| ≤ C := by
    calc
      |favg d - g z| = |(favg d - (n:ℝ)*H 0)+((n:ℝ)*H 0-g z)| := by congr 1; ring
      _ ≤ |favg d - (n:ℝ)*H 0| + |(n:ℝ)*H 0-g z| := abs_add_le _ _
      _ ≤ |slope|+2*L := add_le_add hsupport (by simpa only [abs_sub_comm] using hshapeBound)
      _ = C := rfl
  have hsample : |g z - lastPassage ω 0 d| ≤ (ε/2)*(n:ℝ) := by
    have hh := hs d (by rw [hgeom.1]; exact hns)
    rw [hgeom.1] at hh
    simpa only [abs_sub_comm] using hh
  have htotal : |favg d - lastPassage ω 0 d| ≤ C+(ε/2)*(n:ℝ) := by
    calc
      |favg d - lastPassage ω 0 d| = |(favg d-g z)+(g z-lastPassage ω 0 d)| := by congr 1; ring
      _ ≤ |favg d-g z|+|g z-lastPassage ω 0 d| := abs_add_le _ _
      _ ≤ C+(ε/2)*(n:ℝ) := add_le_add hdet hsample
  have hcsmall : C/(n:ℝ) < ε/2 := by
    have hh := hc n hnc
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg hC hnpos.le)] at hh
    exact hh
  change dist ((favg d-lastPassage ω 0 d)/(n:ℝ)) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hnpos]
  apply (div_lt_iff₀ hnpos).2
  have hcprod : C < (ε/2)*(n:ℝ) := (div_lt_iff₀ hnpos).1 hcsmall
  linarith

/-- Every maximizing path has exactly the maximum defect, with the
terminal vertex excluded from the weight sum. The maximizing equality is an
explicit premise. -/
theorem maximizing_path_average_defect_eq (ω : Environment) (a G dl dr : ℝ)
    (d : ℕ × ℕ) (p : Path 0 d) (hp : pathWeight ω p = lastPassage ω 0 d) :
    let favg : ℝ := G*((d.1:ℝ)+(d.2:ℝ))+((dl+dr)/2)*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))
    favg - pathWeight ω p = favg - lastPassage ω 0 d ∧
      pathWeight ω p = ∑ i : Fin (d.1+d.2), ω (p.vertex i.castSucc) := by
  exact ⟨congrArg (_ - ·) hp, rfl⟩

/-- Maximum attainment over the finite set of paths gives a geodesic for every
floor endpoint; no sequence of choices is introduced. -/
theorem exists_maximizing_floor_direction_path (ω : Environment) (a : ℝ) (n : ℕ) :
    let d : ℕ × ℕ := (⌊(n : ℝ)*a⌋₊,n-⌊(n : ℝ)*a⌋₊)
    ∃ p : Path 0 d, pathWeight ω p = lastPassage ω 0 d := by
  exact exists_pathWeight_eq_lastPassage ω 0 _


/-- Existence and uniqueness of the shape function under the negative moment and
positive tail conditions. On the same sample event, the geodesic defect is
sublinear in every interior direction. Uniqueness uses the uniform sample
characterization of competitors. -/
theorem exists_unique_shape_with_sublinear_geodesic_defect_of_negative_moment_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        g (c * x.1,c * x.2) = (c : ℝ) * g x) ∧
      (∀ (x y : Quadrant) (r s : ℝ≥0), r+s=1 →
        (r : ℝ)*g x+(s : ℝ)*g y ≤
          g (r*x.1+s*y.1,r*x.2+s*y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ,
        (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
          ∀ d : ℕ × ℕ, N ≤ d.1+d.2 →
            |lastPassage ω 0 d - g ((d.1:ℝ≥0),(d.2:ℝ≥0))| ≤
              ε*((d.1+d.2:ℕ):ℝ)) ∧
        ∀ a : ℝ, 0 < a → a < 1 →
          let H : ℝ → ℝ := fun h => quadrantExtension g (a+h,1-a-h)
          let dl : ℝ := derivWithin H (Iio 0) 0
          let dr : ℝ := derivWithin H (Ioi 0) 0
          let favg : ℕ × ℕ → ℝ := fun d =>
            H 0*((d.1:ℝ)+(d.2:ℝ))+((dl+dr)/2)*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))
          Tendsto (fun n : ℕ =>
            let d : ℕ × ℕ := (⌊(n:ℝ)*a⌋₊,n-⌊(n:ℝ)*a⌋₊)
            (favg d-lastPassage ω 0 d)/(n:ℝ)) atTop (𝓝 0)) := by
  obtain ⟨g,hg,hunique⟩ :=
    exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  refine ⟨g,⟨hg.1,hg.2.1,hg.2.2.1,?_⟩,?_⟩
  · filter_upwards [hg.2.2.2] with ω hω
    refine ⟨hω,?_⟩
    intro a ha0 ha1
    exact floor_direction_geodesic_defect_tendsto g hg.1
      (fun x y r s hrs => hg.2.2.1 x y r s hrs)
      (fun c z => hg.2.1 c z) ω hω a ha0 ha1
  · intro f hf
    apply hunique f
    refine ⟨hf.1,hf.2.1,hf.2.2.1,?_⟩
    filter_upwards [hf.2.2.2] with ω hω
    exact hω.1

end LPPDifferentiability
