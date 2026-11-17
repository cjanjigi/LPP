/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Instances.Int

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- A finite window records the complete greatest-maximizer condition on one segment. -/
private def HasRightmostFiniteWindow
    (ω : Environment) (N : ℕ) (x : Lattice)
    (v : Fin (N + 1) → Lattice) : Prop :=
  ∃ (d : ℕ × ℕ) (p : Path x d),
    ∃ hlength : d.1 + d.2 = N,
      (∀ i : Fin (d.1 + d.2 + 1),
        p.vertex i = v ⟨i.val, by omega⟩) ∧
      pathWeight ω p = lastPassage ω x d ∧
      ∀ q : Path x d,
        pathWeight ω q = lastPassage ω x d →
        ∀ i : Fin (d.1 + d.2 + 1),
          (q.vertex i).1 ≤ (p.vertex i).1 ∧
            (p.vertex i).2 ≤ (q.vertex i).2

private theorem locallyRightmostSegment_iff_window
    (ω : Environment) (γ : ℕ → Lattice) (m N : ℕ) :
    (∃ (d : ℕ × ℕ) (p : Path (γ m) d),
      d.1 + d.2 = N ∧
      (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = γ (m + i.val)) ∧
      pathWeight ω p = lastPassage ω (γ m) d ∧
      ∀ q : Path (γ m) d,
        pathWeight ω q = lastPassage ω (γ m) d →
        ∀ i : Fin (d.1 + d.2 + 1),
          (q.vertex i).1 ≤ (p.vertex i).1 ∧
            (p.vertex i).2 ≤ (q.vertex i).2) ↔
      HasRightmostFiniteWindow ω N (γ m) (fun i => γ (m + i.val)) := by
  constructor
  · rintro ⟨d, p, hlength, htrace, hweight, hgreatest⟩
    refine ⟨d, p, hlength, ?_, hweight, hgreatest⟩
    intro i
    simpa using htrace i
  · rintro ⟨d, p, hlength, htrace, hweight, hgreatest⟩
    refine ⟨d, p, hlength, ?_, hweight, hgreatest⟩
    intro i
    simpa using htrace i

/-- A rooted east/north ray stays in the signed coordinate box at each time. -/
private theorem unitRay_mem_Icc
    {u : Lattice} {γ : ℕ → Lattice}
    (hroot : γ 0 = u)
    (hstep : ∀ n : ℕ,
      γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
        γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ)))
    (n : ℕ) :
    γ n ∈ Set.Icc u (u + ((n : ℤ), (n : ℤ))) := by
  induction n with
  | zero =>
      rw [hroot]
      exact Set.mem_Icc.mpr
        ⟨le_rfl, Prod.le_def.mpr ⟨by simp, by simp⟩⟩
  | succ n ih =>
      have hlowPrev : u ≤ γ n := (Set.mem_Icc.mp ih).1
      have huppPrev : γ n ≤ u + ((n : ℤ), (n : ℤ)) :=
        (Set.mem_Icc.mp ih).2
      rcases Prod.le_def.mp hlowPrev with ⟨hlow₁, hlow₂⟩
      rcases Prod.le_def.mp huppPrev with ⟨hupp₁, hupp₂⟩
      have hupp₁' : (γ n).1 ≤ u.1 + (n : ℤ) := by
        simpa only [Prod.fst_add] using hupp₁
      have hupp₂' : (γ n).2 ≤ u.2 + (n : ℤ) := by
        simpa only [Prod.snd_add] using hupp₂
      have hlow : u ≤ γ (n + 1) := by
        rcases hstep n with hEast | hNorth
        · rw [hEast]
          apply Prod.le_def.mpr
          constructor
          · simp only [Prod.fst_add]
            omega
          · simp only [Prod.snd_add]
            omega
        · rw [hNorth]
          apply Prod.le_def.mpr
          constructor
          · simp only [Prod.fst_add]
            omega
          · simp only [Prod.snd_add]
            omega
      have hupp : γ (n + 1) ≤ u + (((n + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)) := by
        rcases hstep n with hEast | hNorth
        · rw [hEast]
          apply Prod.le_def.mpr
          constructor
          · simp only [Prod.fst_add, Nat.cast_succ]
            omega
          · simp only [Prod.snd_add, Nat.cast_succ]
            omega
        · rw [hNorth]
          apply Prod.le_def.mpr
          constructor
          · simp only [Prod.fst_add, Nat.cast_succ]
            omega
          · simp only [Prod.snd_add, Nat.cast_succ]
            omega
      exact Set.mem_Icc.mpr ⟨hlow, hupp⟩

/-- For each fixed environment and signed root, locally rightmost geodesic rays
form a compact set. Strong Existence manuscript, line 1449. -/
theorem isCompact_locallyRightmostGeodesics
    (ω : LPPDifferentiability.Environment) (u : Lattice) :
    IsCompact {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} := by
  -- The integer metric separates distinct sites, so each finite lattice window is discrete.
  let : DiscreteTopology ℤ :=
    DiscreteTopology.of_forall_le_dist (zero_lt_one : (0 : ℝ) < 1)
      Int.pairwise_one_le_dist
  let : DiscreteTopology Lattice := inferInstance

  let rootRay : Set (ℕ → Lattice) := {γ | γ 0 = u}
  let stepRay : Set (ℕ → Lattice) :=
    {γ | ∀ n : ℕ,
      γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
        γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ))}
  let segmentRay : Set (ℕ → Lattice) :=
    {γ | ∀ m N : ℕ, 0 < N →
      HasRightmostFiniteWindow ω N (γ m) (fun i => γ (m + i.val))}

  -- The root condition is a closed condition on the zeroth coordinate.
  have hrootClosed : IsClosed rootRay := by
    change IsClosed ((fun γ : ℕ → Lattice => γ 0) ⁻¹' ({u} : Set Lattice))
    exact (isClosed_discrete _).preimage (continuous_apply 0)

  -- Each unit-step condition is a closed condition on two coordinates.
  have hstepClosed (n : ℕ) :
      IsClosed {γ : ℕ → Lattice |
        γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
          γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ))} := by
    let stepMap : (ℕ → Lattice) → Lattice × Lattice :=
      fun γ => (γ n, γ (n + 1))
    have hstepMap : Continuous stepMap :=
      (continuous_apply n).prodMk (continuous_apply (n + 1))
    change IsClosed
      (stepMap ⁻¹' {z : Lattice × Lattice |
        z.2 = z.1 + ((1 : ℤ), (0 : ℤ)) ∨
          z.2 = z.1 + ((0 : ℤ), (1 : ℤ))})
    exact (isClosed_discrete _).preimage hstepMap
  have hstepRayClosed : IsClosed stepRay := by
    rw [show stepRay =
      ⋂ n : ℕ, {γ : ℕ → Lattice |
        γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
          γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ))} by
      ext γ
      simp [stepRay]]
    exact isClosed_iInter hstepClosed

  -- The full finite-segment clause is a condition on a finite discrete window.
  have hwindowClosed (m N : ℕ) :
      IsClosed {γ : ℕ → Lattice |
        0 < N → HasRightmostFiniteWindow ω N (γ m) (fun i => γ (m + i.val))} := by
    let windowMap : (ℕ → Lattice) → Lattice × (Fin (N + 1) → Lattice) :=
      fun γ => (γ m, fun i => γ (m + i.val))
    have hvalues : Continuous
        (fun γ : ℕ → Lattice => fun i : Fin (N + 1) => γ (m + i.val)) := by
      apply continuous_pi
      intro i
      exact continuous_apply (m + i.val)
    have hwindowMap : Continuous windowMap :=
      (continuous_apply m).prodMk hvalues
    let goodWindows : Set (Lattice × (Fin (N + 1) → Lattice)) :=
      {w | 0 < N → HasRightmostFiniteWindow ω N w.1 w.2}
    change IsClosed (windowMap ⁻¹' goodWindows)
    exact (isClosed_discrete _).preimage hwindowMap
  have hsegmentRayClosed : IsClosed segmentRay := by
    rw [show segmentRay =
      ⋂ m : ℕ, ⋂ N : ℕ, {γ : ℕ → Lattice |
        0 < N → HasRightmostFiniteWindow ω N (γ m) (fun i => γ (m + i.val))} by
      ext γ
      simp [segmentRay]]
    exact isClosed_iInter fun m => isClosed_iInter fun N => hwindowClosed m N

  -- The finite-window clauses are equivalent to the literal source clauses.
  have hraySet :
      {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} =
        rootRay ∩ (stepRay ∩ segmentRay) := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, rootRay, stepRay, segmentRay,
      IsLocallyRightmostGeodesic]
    constructor
    · rintro ⟨hroot, hstep, hsegment⟩
      refine ⟨hroot, hstep, ?_⟩
      intro m N hN
      exact (locallyRightmostSegment_iff_window ω γ m N).mp (hsegment m N hN)
    · rintro ⟨hroot, hstep, hsegment⟩
      refine ⟨hroot, hstep, ?_⟩
      intro m N hN
      exact (locallyRightmostSegment_iff_window ω γ m N).mpr (hsegment m N hN)
  have hclosed : IsClosed {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} := by
    rw [hraySet]
    exact hrootClosed.inter (hstepRayClosed.inter hsegmentRayClosed)

  -- The ray set lies in a product of finite signed boxes.
  let coordinateBox : ℕ → Set Lattice :=
    fun n => Set.Icc u (u + ((n : ℤ), (n : ℤ)))
  have hboxCompact : ∀ n : ℕ, IsCompact (coordinateBox n) := by
    intro n
    exact (Set.finite_Icc _ _).isCompact
  let boundedRays : Set (ℕ → Lattice) := Set.pi Set.univ coordinateBox
  have hboundedCompact : IsCompact boundedRays := isCompact_univ_pi hboxCompact
  have hcontained :
      {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} ⊆ boundedRays := by
    intro γ hγ n hn
    exact unitRay_mem_Icc hγ.1 hγ.2.1 n
  exact hboundedCompact.of_isClosed_subset hclosed hcontained

end LPP.Busemann
