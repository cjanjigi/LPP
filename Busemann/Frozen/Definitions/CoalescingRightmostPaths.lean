module

public import Busemann.Frozen.Definitions.RightmostCocyclePath

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- All e1-tiebreak paths eventually agree at the same absolute levels. The two local
starting times are aligned explicitly. Strong Existence, lines 177–179 and 448–451. -/
def HasCoalescingRightmostPaths {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Lattice → Lattice → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ u v : Lattice, ∃ m n : ℕ,
    u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
    ∀ k : ℕ,
      rightmostCocyclePath (fun x y => B x y ω) u (m + k) =
      rightmostCocyclePath (fun x y => B x y ω) v (n + k)

end LPP.Busemann
