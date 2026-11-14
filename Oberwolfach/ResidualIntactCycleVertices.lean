module

public import Oberwolfach.ResidualPathIncidentEdge

@[expose] public section
/-! If every edge of a cycle survives, all its vertices survive as well. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem intact_cycle_vertices_survive (H:SimpleGraph V) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y) (a:V) (xs:List V) (hlen:2≤(a::xs).length)
    (hkeep:∀ e∈prescribedOrderedPathEdges ((a::xs)++[a]),e∈H.edgeFinset):
    (a::xs).toFinset⊆R := by
  intro x hx
  obtain ⟨y,hy⟩:=ordered_path_vertex_incident_edge (a::xs) x hlen (List.mem_toFinset.mp hx)
  let u:=(a::xs).getLast (by simp)
  have hlast:(a::xs).getLast?=some u := List.getLast?_eq_getLast_of_ne_nil (by simp)
  have hclose:=ordered_path_append_closing_edge (a::xs) a u hlast
  have he:s(x,y)∈prescribedOrderedPathEdges ((a::xs)++[a]) := by
    rw [hclose]
    exact Finset.mem_insert_of_mem hy
  have hadj:H.Adj x y := by
    have hh:=hkeep s(x,y) he
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hh
  by_contra hn
  exact hisol x hn y hadj
end Oberwolfach
