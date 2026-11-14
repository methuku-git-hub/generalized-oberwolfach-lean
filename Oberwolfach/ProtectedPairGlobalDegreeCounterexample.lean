module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic

@[expose] public section
/-! A finite symmetric edge relation can avoid all internal edges of a
protected set and have low outside degrees while its degree at a protected
vertex is larger. This does not assert that the specific packing is a star. -/
set_option autoImplicit false
namespace Oberwolfach

def protectedPairStarEdges : Finset (Fin 4 × Fin 4) :=
  {(0,1),(1,0),(0,2),(2,0),(0,3),(3,0)}

def protectedPairStarNeighbours (x:Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun y => (x,y)∈protectedPairStarEdges)

theorem protected_pair_outside_degree_does_not_control_global :
    (∀ x y:Fin 4, x∈({0}:Finset (Fin 4)) → y∈({0}:Finset (Fin 4)) →
      (x,y)∉protectedPairStarEdges) ∧
    (∀ x:Fin 4, x∉({0}:Finset (Fin 4)) → (protectedPairStarNeighbours x).card≤1) ∧
    (protectedPairStarNeighbours 0).card=3 ∧
    (∀ x y:Fin 4,(x,y)∈protectedPairStarEdges ↔ (y,x)∈protectedPairStarEdges) := by
  decide
end Oberwolfach
