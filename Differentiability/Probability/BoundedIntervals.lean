/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.BoundedIntervalAssembly
import Mathlib.Tactic

/-!
# Simultaneous bounded-weight level intervals

Lemma 3.2 of the differentiability preprint joins all pairs of endpoints in
two deterministic level intervals. This file assembles its bounded-weight
form on the original probability space.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/
public section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace LPPDifferentiability

/-- Boundedness supplies a positive radius, an actual mean and the shape inputs. -/
theorem bounded_marginal_shape_inputs (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hbound : ∃ M : ℝ, ∀ᵐ x ∂μ, |x|≤M) :
    ∃ M : ℝ, 0<M ∧ (∀ᵐ x ∂μ, |x|≤M) ∧ Integrable (fun x : ℝ => x) μ ∧
      (∃ p : ℝ, 1<p ∧ (∫⁻ x, ENNReal.ofReal ((max (-x) 0)^p) ∂μ)<∞) ∧
      (∫⁻ t in Ioi (0:ℝ), (μ (Ioi t))^(1/2:ℝ))<∞ := by
  obtain ⟨M0,hb⟩ := hbound
  let M : ℝ := |M0|+1
  have hM : 0<M := by dsimp [M]; positivity
  have hMb : ∀ᵐ x ∂μ, |x|≤M := hb.mono fun x hx => by
    dsimp [M]
    linarith only [hx,le_abs_self M0]
  refine ⟨M,hM,hMb,integrable_id_of_ae_abs_le μ M hMb,⟨2,by norm_num,?_⟩,?_⟩
  · have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal ((max (-x) 0)^(2:ℝ))≤ENNReal.ofReal (M^2) := by
      filter_upwards [hMb] with x hx
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_two]
      have hm : max (-x) 0≤M := max_le ((neg_le_abs x).trans hx) hM.le
      have hm0 : 0≤max (-x) 0 := le_max_right _ _
      exact (sq_le_sq₀ hm0 hM.le).2 hm
    calc
      _ ≤ ∫⁻ _x : ℝ, ENNReal.ofReal (M^2) ∂μ := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (M^2) := by simp
      _ < ∞ := ENNReal.ofReal_lt_top
  · exact (integrated_positive_sqrt_tail_le_of_ae_abs_le μ M hM.le hMb).trans_lt
      ENNReal.ofReal_lt_top

/-- One unique actual shape and one success function work for every deterministic
signed pair of closed level intervals at all sufficiently large scales. -/
theorem exists_unique_shape_with_bounded_intervals
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hbound : ∃ M : ℝ, ∀ᵐ x ∂μ, |x|≤M) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c*x.1,c*x.2)=(c:ℝ)*g x) ∧
      (∀ (x y : Quadrant) (r t : ℝ≥0), r+t=1 →
        (r:ℝ)*g x+(t:ℝ)*g y≤g (r*x.1+t*y.1,r*x.2+t*y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0<ε →
        ∃ N : ℕ, 1≤N ∧ ∀ d : ℕ × ℕ, N≤d.1+d.2 →
          |lastPassage ω 0 d-g ((d.1:ℝ≥0),(d.2:ℝ≥0))|≤ε*((d.1+d.2:ℕ):ℝ)) ∧
      (∀ a : ℝ, 0<a → a<1 → ∀ D : ℝ, 1≤D →
        ∀ theta : ℝ, 0<theta → theta<min a (1-a) →
        ∀ η δ : ℝ, 0<η → 0<δ → ∃ s1 : ℝ, 1≤s1 ∧ ∃ p : ℝ → ℝ,
          (∀ s, 0≤p s ∧ p s≤1) ∧ Tendsto p atTop (𝓝 1) ∧
          ∀ (s : ℝ) (I J : ℤ) (lo hi lo' hi' : ℝ), s1≤s → I<J →
            lo≤hi → lo'≤hi' → s≤((J-I:ℤ):ℝ) → ((J-I:ℤ):ℝ)≤D*s →
            hi-lo≤D*s → hi'-lo'≤D*s →
            (∀ u v : Lattice,
              (u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi) →
              (v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi') →
              |(1-a)*((v.1:ℝ)-(u.1:ℝ))-a*((v.2:ℝ)-(u.2:ℝ))|≤
                (min a (1-a)-theta)*((J-I:ℤ):ℝ)) →
            let E : Set Environment := {ω | ∀ u v : Lattice,
              (u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi) →
              (v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi') →
              ∃ q : Path u ((v.1-u.1).toNat,(v.2-u.2).toNat),
                q.vertex (Fin.last ((v.1-u.1).toNat+(v.2-u.2).toNat))=v ∧
                g (((v.1-u.1).toNat:ℝ≥0),((v.2-u.2).toNat:ℝ≥0))-η*s≤pathWeight ω q ∧
                ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
                  |((q.vertex i).1:ℝ)-((1-t)*(u.1:ℝ)+t*(v.1:ℝ))|+
                  |((q.vertex i).2:ℝ)-((1-t)*(u.2:ℝ)+t*(v.2:ℝ))|≤δ*s}
            MeasurableSet E ∧ p s≤(environmentLaw μ).real E) := by
  obtain ⟨M,hM,hMb,_hmean,hneg,hpos⟩ := bounded_marginal_shape_inputs μ hbound
  obtain ⟨g,hg,_hu⟩ := exists_unique_shape_with_travel μ hneg hpos
  obtain ⟨_g0,_hg0,hunique⟩ := exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  refine ⟨g,⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,?_⟩,?_⟩
  · intro a ha ha1 D hD theta ht hti η δ hη hδ
    obtain ⟨L,hL,hcompare⟩ := attachment_shape_comparison g hg.1 hg.2.2.1 hg.2.1 a theta ha ha1 ht hti
    obtain ⟨sT,_hsT,pT,hpT,htT,htravel⟩ :=
      hg.2.2.2.2 a ha ha1 (2*D) (by linarith) (theta/2) (by positivity) (by linarith) (η/2) δ (by positivity) hδ
    let r : ℝ := L+|∫ x : ℝ, x ∂μ|
    let kappa : ℝ := min (theta/16) (min (δ/4) (η/(16*(r+1))))
    let cutoff : ℝ := max 1 (max (4/(min a (1-a)*kappa))
      (max 16 (max (16/theta) (max (16*r/η) (4/δ)))))
    obtain ⟨hκ,_hκθ,_hκδ,_hκη,hscales⟩ := attachment_scale_bounds a theta δ η L
      (∫ x : ℝ, x ∂μ) ha ha1 ht hti hδ hη hL
    let C : ℝ := 4*(D/kappa+1)/min a (1-a)
    let p : ℝ → ℝ := fun s => max 0 (min 1 (1-(2*D*s+2)*Real.exp (-η^2*s/(32*M^2))-C^2*(1-pT (s/2))))
    have hp := interval_success_function D C hM hη pT htT
    refine ⟨max cutoff (2*sT),?_,p,hp.1,hp.2,?_⟩
    · exact (le_max_left 1 _).trans (le_max_left _ _)
    intro s I J lo hi lo' hi' hs _hIJ hw hw' hlo hhi hwidth hwidth' hcone E
    have hsc : cutoff≤s := (le_max_left _ _).trans hs
    have hs1 : 1≤s := (le_max_left 1 _).trans hsc
    have hs0 : 0<s := lt_of_lt_of_le zero_lt_one hs1
    obtain ⟨hmlo,_hmhi,hspacing,hcut1,hcut2,hloss,htube,hms⟩ := hscales s hsc
    let m := Nat.ceil (kappa*s)
    have hm0 : 0<m := by
      by_contra h
      have hz : m=0 := by omega
      change 1≤min a (1-a)*(m:ℝ)/4 at hspacing
      rw [hz,Nat.cast_zero,mul_zero,zero_div] at hspacing
      norm_num at hspacing
    have hst : sT≤s/2 := by have hh := (le_max_right cutoff (2*sT)).trans hs; linarith
    refine ⟨measurableSet_all_interval_paths g a η δ s lo hi lo' hi' I J,?_⟩
    apply bounded_intervals_at_scale μ g a D theta η δ M L kappa s m ha ha1 hD ht hη hM hs0 hκ
      hMb hm0 hms hmlo hspacing hcut1 hcut2 hloss htube
    · intro d e f hdlo hdhi hc he hf
      exact (hcompare s D hs0 hD (d.1+d.2) d e f m rfl hdlo hdhi hc he hf hcut1 hcut2).2.2
    · exact hpT
    · intro u d hdlo hdhi hc
      have hh := htravel (s/2) u d hst hdlo (by convert hdhi using 1; ring) hc
      simpa only [show (η/2)*(s/2)=η*s/4 by ring,show δ*(s/2)=δ*s/2 by ring] using hh
    · exact hw
    · exact hw'
    · exact hwidth
    · exact hwidth'
    · exact hlo
    · exact hhi
    · exact hcone
  · intro f hf
    exact (hunique f ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩).trans
      (hunique g ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1⟩).symm

end LPPDifferentiability
