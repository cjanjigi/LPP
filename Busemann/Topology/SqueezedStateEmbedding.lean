/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.SqueezedStateTopologicalSpace

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

private theorem compressReal_abs_lt_one (x : ℝ) :
    |compressReal x| < 1 := by
  have hden : 0 < 1 + |x| := by positivity
  rw [compressReal, abs_div, abs_of_pos hden]
  exact (div_lt_one hden).2 (by linarith [abs_nonneg x])

private theorem compressReal_recover (x : ℝ) :
    compressReal x / (1 - |compressReal x|) = x := by
  have hden : 1 + |x| ≠ 0 := ne_of_gt (by positivity)
  have habs : |compressReal x| = |x| / (1 + |x|) := by
    rw [compressReal, abs_div, abs_of_pos (by positivity : 0 < 1 + |x|)]
  have hrest : 1 - |compressReal x| = 1 / (1 + |x|) := by
    rw [habs]
    field_simp [hden]; ring
  rw [hrest, compressReal]
  field_simp [hden]

private theorem compressReal_injective : Function.Injective compressReal := by
  intro x y hxy
  have hrecover := congrArg (fun z : ℝ => z / (1 - |z|)) hxy
  simpa only [compressReal_recover] using hrecover

private theorem squeezeScale_pos (t : ℝ) : 0 < squeezeScale t := by
  rw [squeezeScale]
  positivity

/-- The literal squeezed embedding distinguishes all finite states and both poles. -/
theorem squeezedStateEmbedding_injective (J : Type*) :
    Function.Injective (squeezedStateEmbedding J) := by
  intro x y hxy
  cases x with
  | bottom =>
      cases y with
      | bottom => rfl
      | top =>
          have htime : (-1 : ℝ) = 1 := by
            simpa [squeezedStateEmbedding] using congrArg Prod.fst hxy
          norm_num at htime
      | finite state t =>
          have htime : (-1 : ℝ) = compressReal t := by
            simpa [squeezedStateEmbedding] using congrArg Prod.fst hxy
          have hlower := (abs_lt.mp (compressReal_abs_lt_one t)).1
          linarith
  | top =>
      cases y with
      | bottom =>
          have htime : (1 : ℝ) = -1 := by
            simpa [squeezedStateEmbedding] using congrArg Prod.fst hxy
          norm_num at htime
      | top => rfl
      | finite state t =>
          have htime : (1 : ℝ) = compressReal t := by
            simpa [squeezedStateEmbedding] using congrArg Prod.fst hxy
          have hupper := (abs_lt.mp (compressReal_abs_lt_one t)).2
          linarith
  | finite state t =>
      cases y with
      | bottom =>
          have htime : compressReal t = -1 := by
            simpa [squeezedStateEmbedding] using congrArg Prod.fst hxy
          have hlower := (abs_lt.mp (compressReal_abs_lt_one t)).1
          linarith
      | top =>
          have htime : compressReal t = 1 := by
            simpa [squeezedStateEmbedding] using congrArg Prod.fst hxy
          have hupper := (abs_lt.mp (compressReal_abs_lt_one t)).2
          linarith
      | finite otherState s =>
          have hcompressedTime : compressReal t = compressReal s := by
            simpa [squeezedStateEmbedding] using congrArg Prod.fst hxy
          have htime : t = s := compressReal_injective hcompressedTime
          have hcoordinates :
              (fun i => squeezeScale t * compressReal (state i)) =
                (fun i => squeezeScale s * compressReal (otherState i)) := by
            simpa [squeezedStateEmbedding] using congrArg Prod.snd hxy
          have hcoordinates' :
              (fun i => squeezeScale t * compressReal (state i)) =
                (fun i => squeezeScale t * compressReal (otherState i)) := by
            simpa [htime] using hcoordinates
          have hstate : state = otherState := by
            funext i
            apply compressReal_injective
            exact mul_left_cancel₀ (ne_of_gt (squeezeScale_pos t))
              (congrFun hcoordinates' i)
          subst s
          subst otherState
          rfl

end LPP.Busemann
