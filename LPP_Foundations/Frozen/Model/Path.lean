module

public import LPP_Foundations.Frozen.Model.Lattice

@[expose] public section

namespace LPPDifferentiability

/-- A finite up-right path from u to u + d. Local time k has absolute level level(u) + k. -/
structure Path (u : Lattice) (d : ℕ × ℕ) where
  vertex : Fin (d.1 + d.2 + 1) → Lattice
  start : vertex 0 = u
  finish : vertex (Fin.last (d.1 + d.2)) = u + ((d.1 : ℤ), (d.2 : ℤ))
  step : ∀ i : Fin (d.1 + d.2),
    vertex i.succ = vertex i.castSucc + (1, 0) ∨
    vertex i.succ = vertex i.castSucc + (0, 1)

end LPPDifferentiability
