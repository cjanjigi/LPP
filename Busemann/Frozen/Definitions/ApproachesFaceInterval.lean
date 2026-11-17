-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Busemann.Frozen.Definitions.InteriorDirection
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

open LPPDifferentiability Filter
open scoped Topology

namespace LPP.Busemann

/-- GRS arXiv:1510.00860v2, (3.8): escaping endpoints whose normalized
horizontal coordinates have limit inferior and superior inside the face
interval. Only finitely many early terms can have zero level. -/
def approachesFaceInterval (v : ℕ → ℕ × ℕ)
    (left right : InteriorDirection) : Prop :=
  Tendsto (fun n => (v n).1 + (v n).2) atTop atTop ∧
  (left.1.1 : ℝ) ≤
    liminf (fun n : ℕ =>
      ((v n).1 : ℝ) / (((v n).1 + (v n).2 : ℕ) : ℝ)) atTop ∧
  limsup (fun n : ℕ =>
      ((v n).1 : ℝ) / (((v n).1 + (v n).2 : ℕ) : ℝ)) atTop ≤
    (right.1.1 : ℝ)

end LPP.Busemann
