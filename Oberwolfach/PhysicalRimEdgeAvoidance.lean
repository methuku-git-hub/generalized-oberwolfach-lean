module

public import Oberwolfach.PartialFactorWalkEdgeDisjointnessPoly
public import Oberwolfach.PhysicalEdgeGraph

@[expose] public section
/-! A map into the physical rim graph is edge-disjoint from a map whose
source-edge images avoid that rim set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem partial_map_edges_inside_physical_rim
    {X V:Type*} [Fintype V] [DecidableEq V]
    (F:SimpleGraph X) (R:Finset (Finset V)) (f:X→V)
    (hmap:∀x y,F.Adj x y→(physicalEdgeGraph R).Adj (f x) (f y)) :
    ∀e∈partialFactorPhysicalEdgesPoly X F f,e.toFinset∈R := by
  intro e he
  obtain ⟨x,y,hxy,rfl⟩:=he
  simpa only [Sym2.toFinset_mk_eq] using (hmap x y hxy).2

theorem partial_maps_disjoint_of_physical_rim_avoidance
    {X Z V:Type*} [Fintype V] [DecidableEq V]
    (F:SimpleGraph X) (Q:SimpleGraph Z) (R:Finset (Finset V)) (f:X→V) (g:Z→V)
    (hmap:∀x y,F.Adj x y→(physicalEdgeGraph R).Adj (f x) (f y))
    (havoid:∀x y,Q.Adj x y→({g x,g y}:Finset V)∉R) :
    Disjoint (partialFactorPhysicalEdgesPoly X F f) (partialFactorPhysicalEdgesPoly Z Q g) := by
  apply Set.disjoint_left.mpr
  intro e he hf
  have heR:=partial_map_edges_inside_physical_rim F R f hmap e he
  obtain ⟨x,y,hxy,rfl⟩:=hf
  apply havoid x y hxy
  simpa only [Sym2.toFinset_mk_eq] using heR
end Oberwolfach
