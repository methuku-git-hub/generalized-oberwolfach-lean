module

public import Oberwolfach.ResidualCycleIncomingArc
public import Oberwolfach.PrescribedCycleRotate
public import Oberwolfach.PrescribedPieceArcPhysical

@[expose] public section
/-! Rotate an ordered cycle so that a deleted edge is the closing edge,
without changing the chosen source orientation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem cycle_rotate_deleted_edge_to_closure (H:SimpleGraph V) (D:V→V→Prop)
    (a:V) (xs:List V) (hn:(a::xs).Nodup)
    (e:Sym2 V) (he:e∈prescribedOrderedPathEdges ((a::xs)++[a]))
    (hmissing:e∉H.edgeFinset):
    ∃ (v u:V) (ys:List V),
      (v::ys).Nodup ∧ (a::xs).toFinset=(v::ys).toFinset ∧
      (List.IsChain D ((a::xs)++[a]) ↔ List.IsChain D ((v::ys)++[v])) ∧
      prescribedOrderedPathEdges ((a::xs)++[a])=prescribedOrderedPathEdges ((v::ys)++[v]) ∧
      prescribedDirectedPathEdges ((a::xs)++[a])=prescribedDirectedPathEdges ((v::ys)++[v]) ∧
      (v::ys).getLast?=some u ∧ ¬H.Adj u v := by
  rw [prescribed_ordered_edges_are_arc_images] at he
  obtain ⟨arc,harc,heq⟩:=Finset.mem_image.mp he
  rcases arc with ⟨u,v⟩
  have heq':s(u,v)=e := heq
  have hnot:¬H.Adj u v := by
    intro h
    apply hmissing
    rw [←heq']
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using h
  have hverts:=prescribed_directed_path_edge_endpoints ((a::xs)++[a]) (u,v) harc
  have hv:v∈a::xs := by simpa [or_assoc,or_left_comm,or_comm] using hverts.2
  by_cases hva:v=a
  · subst v
    refine ⟨a,u,xs,hn,rfl,Iff.rfl,rfl,rfl,?_,hnot⟩
    exact directed_cycle_incoming_arc_is_closing a u xs hn harc
  · have hv':v∈xs := by simpa [hva] using hv
    obtain ⟨ys,hn',_,hset,hchain,hphys,hdir⟩:=prescribed_cycle_rotate a v xs hn hv' D
    have hrot:(u,v)∈prescribedDirectedPathEdges ((v::ys)++[v]) := by rw [←hdir];exact harc
    exact ⟨v,u,ys,hn',hset,hchain,hphys,hdir,directed_cycle_incoming_arc_is_closing v u ys hn' hrot,hnot⟩
end Oberwolfach
