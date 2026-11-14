module

public import Oberwolfach.MarkedPhysicalHostGraph

@[expose] public section
/-! A physical graph built from ordinary and marked rim arcs is a subgraph
of any host containing those actual edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem host_adj_of_equal_physical_pair
    {V:Type*} [DecidableEq V] (H:SimpleGraph V) (a b x y:V)
    (hxy:x≠y) (heq:({a,b}:Finset V)={x,y}) (hab:H.Adj a b) : H.Adj x y := by
  have hx:x∈({a,b}:Finset V):=by rw [heq];simp
  have hy:y∈({a,b}:Finset V):=by rw [heq];simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
  · exact (hxy rfl).elim
  · exact hab
  · exact hab.symm
  · exact (hxy rfl).elim

theorem marked_physical_host_graph_le
    {V E K:Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype K]
    (H:SimpleGraph V) (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hE:∀e,H.Adj (tail e) (head e)) (hK:∀e,H.Adj (ktail e) (π (khead e))) :
    physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π) ≤ H := by
  intro x y hxy
  obtain ⟨e,_,heq⟩:=Finset.mem_image.mp hxy.2
  cases e with
  | inl e =>
    apply host_adj_of_equal_physical_pair H (tail e) (head e) x y hxy.1 ?_ (hE e)
    simpa only [markedPhysicalEdge,Sum.elim_inl] using heq
  | inr e =>
    apply host_adj_of_equal_physical_pair H (ktail e) (π (khead e)) x y hxy.1 ?_ (hK e)
    simpa only [markedPhysicalEdge,Sum.elim_inr] using heq

theorem marked_partial_map_lifts_to_host
    {V E K X:Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype K]
    (H:SimpleGraph V) (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hE:∀e,H.Adj (tail e) (head e)) (hK:∀e,H.Adj (ktail e) (π (khead e)))
    (F:SimpleGraph X) (f:X→V)
    (hmap:∀x y,F.Adj x y→(physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)).Adj (f x) (f y)) :
    ∀x y,F.Adj x y→H.Adj (f x) (f y) := by
  intro x y hxy
  exact marked_physical_host_graph_le H tail head ktail khead π hE hK (hmap x y hxy)
end Oberwolfach
