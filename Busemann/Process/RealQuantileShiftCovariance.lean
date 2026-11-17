/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.RealQuantileSamplerLaw
public import Busemann.Process.RightmostPathCovariance

import Busemann.Process.ConditionalPathKernelCovariance
import Busemann.Geometry.GeodesicInfimum
import LPP_Foundations.Model.LastPassage.Translate
import Lean.Elab.Tactic.Omega

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal
namespace LPP.Busemann

private theorem pathSoutheastLE_translate_iff
    (γ δ : ℕ → Lattice) (z : Lattice) :
    pathSoutheastLE (fun n => γ n + z) (fun n => δ n + z) ↔
      pathSoutheastLE γ δ := by
  constructor
  · intro h m n hlevel
    have hshiftlevel :
        ((γ 0 + z).1 + (γ 0 + z).2 + (m : ℤ)) =
          ((δ 0 + z).1 + (δ 0 + z).2 + (n : ℤ)) := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    have hmn := h m n hshiftlevel
    simp only [Prod.fst_add, Prod.snd_add] at hmn
    constructor <;> omega
  · intro h m n hlevel
    have hbaselevel :
        (γ 0).1 + (γ 0).2 + (m : ℤ) =
          (δ 0).1 + (δ 0).2 + (n : ℤ) := by
      simp only [Prod.fst_add, Prod.snd_add] at hlevel
      omega
    have hmn := h m n hbaselevel
    simp only [Prod.fst_add, Prod.snd_add]
    constructor <;> omega

private theorem pathSoutheastLE_self (γ : ℕ → Lattice) :
    pathSoutheastLE γ γ := by
  intro m n hlevel
  have hmn : m = n := by omega
  subst n
  exact ⟨le_refl _, le_refl _⟩

private theorem pathSoutheastLE_antisymm_same_root
    (γ δ : ℕ → Lattice) (hroot : γ 0 = δ 0)
    (hγδ : pathSoutheastLE γ δ) (hδγ : pathSoutheastLE δ γ) :
    γ = δ := by
  have hf := (pathSoutheastLE_iff_all_times_of_same_root γ δ hroot).mp hγδ
  have hb := (pathSoutheastLE_iff_all_times_of_same_root δ γ hroot.symm).mp hδγ
  funext n
  exact Prod.ext (le_antisymm (hf n).1 (hb n).1)
    (le_antisymm (hb n).2 (hf n).2)

private theorem locallyRightmostGeodesic_translate
    (ω : Environment) (u z : Lattice) (γ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic (environmentTranslationEquiv z ω) u γ) :
    IsLocallyRightmostGeodesic ω (z + u) (fun n => z + γ n) := by
  rcases hγ with ⟨hstart, hstep, hsegments⟩
  refine ⟨by simp [hstart], ?_, ?_⟩
  · intro n
    rcases hstep n with h | h
    · left
      simp only [h, add_assoc]
    · right
      simp only [h, add_assoc]
  · intro m N hN
    obtain ⟨d, p, hd, hpvertex, hpweight, hpmax⟩ := hsegments m N hN
    refine ⟨d, p.translate z, hd, ?_, ?_, ?_⟩
    · intro i
      simp only [Path.translate_vertex]
      rw [hpvertex i]
    · calc
        pathWeight ω (p.translate z) =
            pathWeight (environmentTranslationEquiv z ω) p := by
              exact pathWeight_translate ω p z
        _ = lastPassage (environmentTranslationEquiv z ω) (γ m) d := hpweight
        _ = lastPassage ω (z + γ m) d := by
              exact lastPassage_translate ω z (γ m) d
    · intro q hq i
      let q₀ : Path (γ m) d := Path.untranslate z q
      have hq₀ : pathWeight (environmentTranslationEquiv z ω) q₀ =
          lastPassage (environmentTranslationEquiv z ω) (γ m) d := by
        calc
          pathWeight (environmentTranslationEquiv z ω) q₀ =
              pathWeight ω (q₀.translate z) :=
                (pathWeight_translate ω q₀ z).symm
          _ = pathWeight ω q := by rw [Path.translate_untranslate]
          _ = lastPassage ω (z + γ m) d := hq
          _ = lastPassage (environmentTranslationEquiv z ω) (γ m) d :=
            (lastPassage_translate ω z (γ m) d).symm
      have hineq := hpmax q₀ hq₀ i
      have hqvertex : q.vertex i = z + q₀.vertex i := by
        calc
          q.vertex i = (q₀.translate z).vertex i := by rw [Path.translate_untranslate]
          _ = z + q₀.vertex i := rfl
      rw [hqvertex, Path.translate_vertex]
      simp only [Prod.fst_add, Prod.snd_add]
      exact ⟨by omega, by omega⟩

/-- The one real quantile sampler for the original conditional rightmost-path
law is covariant under every lattice shift. Strong Existence, public source
Lemma xBhatproc, equation x-cov, lines 793–840. -/
theorem exists_measurable_real_rightmost_quantile_sampler_with_law_and_shift_covariance
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, P.map (processShift z) = P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B) :
    let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
      fun u => condDistrib
        (fun a : ProcessSample =>
          rightmostCocyclePath (fun x y => B x y a) u)
        processEnvironment P
    ∃ q : Lattice → Environment → unitInterval → (ℕ → Lattice),
      (∀ u : Lattice, Measurable
        (fun a : Environment × unitInterval => q u a.1 a.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic ω u (q u ω s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (q u ω s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ})) ∧
      (∀ u : Lattice,
        (((environmentLaw μ).prod (volume : Measure unitInterval)).map
          (fun a : Environment × unitInterval => (a.1, q u a.1 a.2))) =
        P.map (fun a : ProcessSample =>
          (processEnvironment a,
            rightmostCocyclePath (fun x y => B x y a) u))) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ (u z : Lattice) (s : unitInterval),
        q (u + z) ω s =
          fun n : ℕ => q u (environmentTranslationEquiv z ω) s n + z) := by
  classical
  let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
    fun u => condDistrib
      (fun a : ProcessSample =>
        rightmostCocyclePath (fun x y => B x y a) u)
      processEnvironment P
  obtain ⟨q, hMeas, hCDF, hLaw⟩ :=
    exists_measurable_real_rightmost_quantile_sampler_with_law μ P hMarginal B hB
  refine ⟨q, hMeas, hCDF, hLaw, ?_⟩
  have hKernel : ∀ᵐ ω ∂environmentLaw μ, ∀ u z : Lattice,
      κ (u + z) ω =
        (κ u (environmentTranslationEquiv z ω)).map
          (fun γ : ℕ → Lattice => fun n => γ n + z) :=
    conditional_rightmost_path_law_shift_covariance μ P hMarginal hShift B hB
  have hShiftCDF : ∀ᵐ ω ∂environmentLaw μ,
      ∀ z : Lattice, ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic (environmentTranslationEquiv z ω) u
            (q u (environmentTranslationEquiv z ω) s) ∧
        ∀ γ : ℕ → Lattice,
          IsLocallyRightmostGeodesic (environmentTranslationEquiv z ω) u γ →
          (pathSoutheastLE (q u (environmentTranslationEquiv z ω) s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (κ u) (environmentTranslationEquiv z ω)
                {η : ℕ → Lattice | pathSoutheastLE η γ}) := by
    apply ae_all_iff.mpr
    intro z
    exact (measurePreserving_environmentTranslationEquiv μ z).quasiMeasurePreserving.ae hCDF
  filter_upwards [hCDF, hKernel, hShiftCDF] with ω hGood hCov hGoodShift
  intro u z s
  let Tω := environmentTranslationEquiv z ω
  let a := q (u + z) ω s
  let b := q u Tω s
  let bShift : ℕ → Lattice := fun n => b n + z
  have hGeoA : IsLocallyRightmostGeodesic ω (u + z) a :=
    (hGood (u + z) s).1
  have hGeoB : IsLocallyRightmostGeodesic Tω u b :=
    (hGoodShift z u s).1
  have hGeoBShift : IsLocallyRightmostGeodesic ω (u + z) bShift := by
    simpa only [bShift, add_comm] using
      locallyRightmostGeodesic_translate ω u z b hGeoB
  have hPathMeas : Measurable
      (fun γ : ℕ → Lattice => fun n : ℕ => γ n + z) := by
    apply measurable_pi_iff.mpr
    intro n
    exact (measurable_pi_apply n).add measurable_const
  have hMass (γ : ℕ → Lattice) :
      κ (u + z) ω {η : ℕ → Lattice |
        pathSoutheastLE η (fun n => γ n + z)} =
      κ u Tω {η : ℕ → Lattice | pathSoutheastLE η γ} := by
    have hCut : MeasurableSet {η : ℕ → Lattice |
        pathSoutheastLE η (fun n => γ n + z)} := by
      have hArg : Measurable (fun η : ℕ → Lattice =>
          (η, fun n : ℕ => γ n + z)) :=
        measurable_id.prodMk measurable_const
      exact measurableSet_pathSoutheastLE.preimage hArg
    rw [hCov u z, Measure.map_apply hPathMeas hCut]
    congr 1
    ext η
    exact pathSoutheastLE_translate_iff η γ z
  have hAB : pathSoutheastLE a bShift := by
    apply ((hGood (u + z) s).2 bShift hGeoBShift).2
    rw [hMass b]
    exact ((hGoodShift z u s).2 b hGeoB).1 (pathSoutheastLE_self b)
  let aBack : ℕ → Lattice := fun n => a n + (-z)
  have hEnvBack : environmentTranslationEquiv (-z) Tω = ω := by
    funext x
    simp [Tω, environmentTranslationEquiv_apply]
  have hGeoABack : IsLocallyRightmostGeodesic Tω u aBack := by
    have h := locallyRightmostGeodesic_translate Tω (u + z) (-z) a
      (by simpa only [hEnvBack] using hGeoA)
    simpa [aBack, add_assoc, add_comm, add_left_comm] using h
  have hBackShift : (fun n : ℕ => aBack n + z) = a := by
    funext n
    simp [aBack]
  have hBBackA : pathSoutheastLE b aBack := by
    apply ((hGoodShift z u s).2 aBack hGeoABack).2
    rw [← hMass aBack, hBackShift]
    exact ((hGood (u + z) s).2 a hGeoA).1 (pathSoutheastLE_self a)
  have hBA : pathSoutheastLE bShift a := by
    have h := (pathSoutheastLE_translate_iff b aBack z).2 hBBackA
    simpa only [bShift, hBackShift] using h
  exact pathSoutheastLE_antisymm_same_root a bShift
    (hGeoA.1.trans hGeoBShift.1.symm) hAB hBA

end LPP.Busemann
