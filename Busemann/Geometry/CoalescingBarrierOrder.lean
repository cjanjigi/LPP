/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.GeodesicOrder
public import Busemann.Geometry.GeodesicPrefixOrder
public import Busemann.Geometry.CrossedGeodesicCoalescenceAtRoots
public import LPP_Foundations.Model.Paths.Coalescence
import Lean.Elab.Tactic.Omega

@[expose] public section
open LPPDifferentiability LPP.Busemann

namespace LPP.Busemann

/-- Coalescing locally rightmost rays and barriers have the same southeast
cut at either signed root. Strong Existence, lines 916–927. -/
theorem pathSoutheastLE_iff_of_coalescing_locallyRightmost_pairs
    (ω : Environment) (u v : Lattice)
    (rayU barrierU rayV barrierV : ℕ → Lattice)
    (hRayU : IsLocallyRightmostGeodesic ω u rayU)
    (hBarrierU : IsLocallyRightmostGeodesic ω u barrierU)
    (hRayV : IsLocallyRightmostGeodesic ω v rayV)
    (hBarrierV : IsLocallyRightmostGeodesic ω v barrierV)
    (hRays : paths_coalesce u v rayU rayV)
    (hBarriers : paths_coalesce u v barrierU barrierV) :
    pathSoutheastLE rayU barrierU ↔
      pathSoutheastLE rayV barrierV := by
  classical

  -- A direction of the result only uses the two coalescence witnesses in
  -- their given order; the converse will swap roots and reverse each witness.
  have hDirection
      (a b : Lattice) (γa δa γb δb : ℕ → Lattice)
      (hγa : IsLocallyRightmostGeodesic ω a γa)
      (hδa : IsLocallyRightmostGeodesic ω a δa)
      (hγb : IsLocallyRightmostGeodesic ω b γb)
      (hδb : IsLocallyRightmostGeodesic ω b δb)
      (hRaysAB : paths_coalesce a b γa γb)
      (hBarriersAB : paths_coalesce a b δa δb)
      (hCutA : pathSoutheastLE γa δa) :
      pathSoutheastLE γb δb := by
    -- If the first-root paths agree, their aligned tails force meetings at
    -- arbitrarily late indices at the second root.
    have hEqualAtB (hEqualA : γa = δa) : γb = δb := by
      obtain ⟨mRay, nRay, hRayLevel, hRayTail⟩ := hRaysAB
      obtain ⟨mBarrier, nBarrier, hBarrierLevel, hBarrierTail⟩ := hBarriersAB
      have hIndex : nRay + mBarrier = nBarrier + mRay := by
        omega
      funext k
      let N := nRay + mBarrier + k
      have hMeet : γb N = δb N := by
        dsimp [N]
        calc
          γb (nRay + mBarrier + k) = γa (mRay + (mBarrier + k)) :=
            by simpa only [Nat.add_assoc] using (hRayTail (mBarrier + k)).symm
          _ = γa (mBarrier + (mRay + k)) :=
            congrArg γa (by omega)
          _ = δa (mBarrier + (mRay + k)) :=
            congrArg (fun p : ℕ → Lattice => p (mBarrier + (mRay + k))) hEqualA
          _ = δb (nBarrier + (mRay + k)) :=
            hBarrierTail (mRay + k)
          _ = δb (nRay + mBarrier + k) :=
            congrArg δb (by omega)
      have hPrefix := locallyRightmostGeodesic_eq_prefix_of_meet
        ω b γb δb hγb hδb N hMeet
      exact hPrefix k (by dsimp [N]; omega)

    have hReflγb : pathSoutheastLE γb γb := by
      rcases pathSoutheastLE_total_of_isLocallyRightmostGeodesic
        ω b γb γb hγb hγb with h | h
      · exact h
      · exact h
    have hReflδb : pathSoutheastLE δb δb := by
      rcases pathSoutheastLE_total_of_isLocallyRightmostGeodesic
        ω b δb δb hδb hδb with h | h
      · exact h
      · exact h

    by_cases hEqualA : γa = δa
    · have hEqualB := hEqualAtB hEqualA
      rw [hEqualB]
      exact hReflδb
    · -- If the second-root cut fails, totality makes its reverse order strict.
      by_contra hNotCutB
      have hOrderB := pathSoutheastLE_total_of_isLocallyRightmostGeodesic
        ω b γb δb hγb hδb
      have hReverseB : pathSoutheastLE δb γb := hOrderB.resolve_left hNotCutB
      have hDistinctB : δb ≠ γb := by
        intro hEqualB
        apply hNotCutB
        rw [hEqualB]
        exact hReflγb

      -- Opposite strict orders around the coalescing barriers forbid the
      -- supplied outer-ray coalescence.
      have hNoOuter := no_outer_coalescence_of_crossed_locallyRightmost_rays_at_roots
        ω a b γa δa δb γb hγa hδa hδb hγb
        ⟨hCutA, hEqualA⟩ ⟨hReverseB, hDistinctB⟩ hBarriersAB
      exact hNoOuter hRaysAB

  -- Reverse both aligned-tail witnesses for the converse implication.
  have hRaysReverse : paths_coalesce v u rayV rayU :=
    paths_coalesce_symm u v rayU rayV hRays
  have hBarriersReverse : paths_coalesce v u barrierV barrierU :=
    paths_coalesce_symm u v barrierU barrierV hBarriers

  constructor
  · exact hDirection u v rayU barrierU rayV barrierV
      hRayU hBarrierU hRayV hBarrierV hRays hBarriers
  · exact hDirection v u rayV barrierV rayU barrierU
      hRayV hBarrierV hRayU hBarrierU hRaysReverse hBarriersReverse

end LPP.Busemann
