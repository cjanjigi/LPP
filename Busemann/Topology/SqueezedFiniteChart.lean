/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Topology.SqueezedStateLimits
public import Mathlib.Topology.Maps.Basic

/-!
# The finite squeezed-state chart

The induced topology on squeezed states recovers the original time and each
real state coordinate at a finite state.
-/

@[expose] public section

namespace LPP.Busemann

private theorem abs_compressReal_lt_one (a : ℝ) : |compressReal a| < 1 := by
  have hden : 0 < 1 + |a| := by linarith [abs_nonneg a]
  rw [compressReal, abs_div, abs_of_pos hden]
  rw [div_lt_one hden]
  linarith [abs_nonneg a]

private theorem squeezeScale_eq_one_sub_abs_compressReal (a : ℝ) :
    squeezeScale a = 1 - |compressReal a| := by
  have hden : 0 < 1 + |a| := by linarith [abs_nonneg a]
  have hne : 1 + |a| ≠ 0 := ne_of_gt hden
  rw [squeezeScale, compressReal, abs_div, abs_of_pos hden]
  field_simp
  ring

private theorem decode_compressReal (a : ℝ) :
    compressReal a / (1 - |compressReal a|) = a := by
  have hden : 0 < 1 + |a| := by linarith [abs_nonneg a]
  have hne : 1 + |a| ≠ 0 := ne_of_gt hden
  rw [← squeezeScale_eq_one_sub_abs_compressReal, compressReal, squeezeScale]
  field_simp

private theorem continuousAt_decode_compressReal (a : ℝ) :
    ContinuousAt (fun u : ℝ => u / (1 - |u|)) (compressReal a) := by
  have hden : 1 - |compressReal a| ≠ 0 :=
    ne_of_gt (by linarith [abs_compressReal_lt_one a])
  exact continuousAt_id.div
    (continuousAt_const.sub continuous_abs.continuousAt) hden

/-- The finite constructor reflects convergence of time and every real state
coordinate in the actual topology induced by `squeezedStateEmbedding`. -/
theorem squeezedState_finite_isEmbedding (J : Type*) :
    Topology.IsEmbedding (fun p : (J → ℝ) × ℝ =>
      (SqueezedState.finite p.1 p.2 : SqueezedState J)) := by
  let F : ((J → ℝ) × ℝ) → ℝ × (J → ℝ) :=
    fun p => (compressReal p.2,
      fun i => squeezeScale p.2 * compressReal (p.1 i))
  let G : (ℝ × (J → ℝ)) → (J → ℝ) × ℝ :=
    fun z =>
      ((fun i =>
          (z.2 i / (1 - |z.1|)) /
            (1 - |z.2 i / (1 - |z.1|)|)),
        z.1 / (1 - |z.1|))
  have hGF : ∀ p : (J → ℝ) × ℝ, G (F p) = p := by
    intro p
    apply Prod.ext
    · funext i
      change
        (squeezeScale p.2 * compressReal (p.1 i) /
          (1 - |compressReal p.2|)) /
          (1 - |squeezeScale p.2 * compressReal (p.1 i) /
            (1 - |compressReal p.2|)|) = p.1 i
      rw [← squeezeScale_eq_one_sub_abs_compressReal p.2]
      have hs : squeezeScale p.2 ≠ 0 := by
        rw [squeezeScale]
        exact one_div_ne_zero (ne_of_gt (by linarith [abs_nonneg p.2]))
      rw [mul_div_cancel_left₀ _ hs]
      exact decode_compressReal (p.1 i)
    · exact decode_compressReal p.2
  have hGcont : ∀ p : (J → ℝ) × ℝ, ContinuousAt G (F p) := by
    intro p
    have hscale : 1 - |compressReal p.2| ≠ 0 :=
      ne_of_gt (by linarith [abs_compressReal_lt_one p.2])
    have htime : ContinuousAt (fun z : ℝ × (J → ℝ) =>
        z.1 / (1 - |z.1|)) (F p) :=
      continuousAt_fst.div
        (continuousAt_const.sub continuousAt_fst.abs) hscale
    have hstate : ContinuousAt (fun z : ℝ × (J → ℝ) =>
        fun i => (z.2 i / (1 - |z.1|)) /
          (1 - |z.2 i / (1 - |z.1|)|)) (F p) := by
      apply continuousAt_pi.mpr
      intro i
      have hw : ContinuousAt (fun z : ℝ × (J → ℝ) =>
          z.2 i / (1 - |z.1|)) (F p) :=
        ((continuous_apply i).comp continuous_snd).continuousAt.div
          (continuousAt_const.sub continuousAt_fst.abs) hscale
      have hw_eq :
          (F p).2 i / (1 - |(F p).1|) = compressReal (p.1 i) := by
        change squeezeScale p.2 * compressReal (p.1 i) /
          (1 - |compressReal p.2|) = compressReal (p.1 i)
        rw [← squeezeScale_eq_one_sub_abs_compressReal p.2]
        have hs : squeezeScale p.2 ≠ 0 := by
          rw [squeezeScale]
          exact one_div_ne_zero (ne_of_gt (by linarith [abs_nonneg p.2]))
        exact mul_div_cancel_left₀ _ hs
      have hdecode := continuousAt_decode_compressReal (p.1 i)
      exact hdecode.comp_of_eq hw hw_eq
    exact hstate.prodMk htime
  have hFcont : Continuous F := by
    change Continuous (fun p : (J → ℝ) × ℝ =>
      (compressReal p.2,
        fun i => squeezeScale p.2 * compressReal (p.1 i)))
    have hc : Continuous compressReal := by
      rw [continuous_iff_continuousAt]
      intro a
      change ContinuousAt (fun b : ℝ => b / (1 + |b|)) a
      exact continuousAt_id.div
        (continuousAt_const.add continuous_abs.continuousAt)
        (ne_of_gt (by linarith [abs_nonneg a]))
    have hs : Continuous squeezeScale := by
      rw [continuous_iff_continuousAt]
      intro a
      change ContinuousAt (fun b : ℝ => (1 : ℝ) / (1 + |b|)) a
      exact continuousAt_const.div
        (continuousAt_const.add continuous_abs.continuousAt)
        (ne_of_gt (by linarith [abs_nonneg a]))
    exact (hc.comp continuous_snd).prodMk
      (continuous_pi fun i =>
        (hs.comp continuous_snd).mul
          (hc.comp ((continuous_apply i).comp continuous_fst)))
  have hFemb : Topology.IsEmbedding F := by
    refine Topology.IsEmbedding.mk' F (fun p q h => ?_) ?_
    · calc
        p = G (F p) := (hGF p).symm
        _ = G (F q) := congrArg G h
        _ = q := hGF q
    · intro p
      apply le_antisymm
      · have ht : Filter.Tendsto (G ∘ F)
            (Filter.comap F (nhds (F p))) (nhds p) := by
          have hcomp := Filter.Tendsto.comp (hGcont p)
            (Filter.tendsto_comap (f := F) (x := nhds (F p)))
          simpa only [hGF] using hcomp
        have heq : G ∘ F = id := funext hGF
        rw [heq] at ht
        change Filter.comap F (nhds (F p)) ≤ nhds p at ht
        exact ht
      · exact hFcont.continuousAt.le_comap
  have hfinite : Continuous (fun p : (J → ℝ) × ℝ =>
      (SqueezedState.finite p.1 p.2 : SqueezedState J)) :=
    continuous_squeezedState_finite J
  have hembedding : Continuous (squeezedStateEmbedding J) := by
    change @Continuous (SqueezedState J) (ℝ × (J → ℝ))
      (squeezedStateTopology J) inferInstance (squeezedStateEmbedding J)
    exact continuous_induced_dom
  apply Topology.IsEmbedding.of_comp hfinite hembedding
  convert hFemb using 1
  funext p
  rfl

end LPP.Busemann
