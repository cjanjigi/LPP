module

public import LPP_Foundations.Frozen.Model.Quadrant

/-!
The literal superdifferential on the full closed quadrant. This includes the
boundary points needed by JR1810.03580v3, Lemma C.2 and Lemma 4.5(b,c).
-/

@[expose] public section

namespace LPPDifferentiability

/-- The superdifferential of `g` at any point of its closed quadrant domain,
with the inequality and domain of JR1810.03580v3, equation (2.5). -/
def quadrantSuperdifferential (g : Quadrant → ℝ) (ξ : Quadrant) :
    Set (ℝ × ℝ) :=
  {v | ∀ z : Quadrant,
    v.1 * ((ξ.1 : ℝ) - (z.1 : ℝ)) +
      v.2 * ((ξ.2 : ℝ) - (z.2 : ℝ)) ≤ g ξ - g z}

end LPPDifferentiability
