module

public import Oberwolfach.LongEligibleMarkedIncomingChange
public import Oberwolfach.PhysicalRimEdgeAvoidance

@[expose] public section
/-! Eligible residual rim arcs avoid every physical edge already packed into
 the complement of the fixed buffered paths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_eligible_rim_avoids_small
    {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
    (M:V→V→ℕ) (Small:SimpleGraph V) (B:Finset (V×V))
    (hB:∀a∈B,longEligibleResidualArc M Small ⊥ a) :
    ∀x y,({x,y}:Finset V)∈B.image (fun a=>({a.1,a.2}:Finset V))→¬Small.Adj x y:=by
  intro x y hxy hs
  obtain ⟨⟨a,b⟩,hab,heq⟩:=Finset.mem_image.mp hxy
  have hna:¬Small.Adj a b:=(hB (a,b) hab).2.1
  have hx:x∈({a,b}:Finset V):=by rw [heq];simp
  have hy:y∈({a,b}:Finset V):=by rw [heq];simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
  · exact (hs.ne rfl).elim
  · exact hna hs
  · exact hna hs.symm
  · exact (hs.ne rfl).elim

theorem long_complement_edges_avoid_eligible_rim
    {X V U:Type} [Fintype X] [Fintype V] [LinearOrder V] [Nonempty V]
    (M:V→V→ℕ) (Small:SimpleGraph V) (B:Finset (V×V))
    (hB:∀a∈B,longEligibleResidualArc M Small ⊥ a)
    (F:U→SimpleGraph X) (f:U→X→V)
    (hPacked:∀u,((F u).edgeFinset.image (Sym2.map (f u)))⊆Small.edgeFinset):
    ∀u x y,(F u).Adj x y→
      ({f u x,f u y}:Finset V)∉B.image (fun a=>({a.1,a.2}:Finset V)):=by
  intro u x y hxy hrim
  have he:s(f u x,f u y)∈Small.edgeFinset:=hPacked u (Finset.mem_image.mpr
    ⟨s(x,y),SimpleGraph.mem_edgeFinset.mpr hxy,rfl⟩)
  exact long_eligible_rim_avoids_small M Small B hB (f u x) (f u y) hrim
    (SimpleGraph.mem_edgeFinset.mp he)
end Oberwolfach
