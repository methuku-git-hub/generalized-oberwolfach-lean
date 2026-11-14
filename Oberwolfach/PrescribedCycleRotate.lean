module

public import Oberwolfach.PrescribedCycleTwoBoundarySplit
public import Mathlib.Data.List.Chain

@[expose] public section
/-! Rotating an ordered source cycle at one of its vertices preserves its
vertices, directed arcs, undirected edges and cyclic chain condition. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]

theorem prescribed_cycle_rotate (a b:X) (xs:List X) (hnodup:(a::xs).Nodup) (hb:b∈xs)
    (R:X→X→Prop):
    ∃ ys:List X,(b::ys).Nodup ∧ (a::xs).length=(b::ys).length ∧ (a::xs).toFinset=(b::ys).toFinset ∧
      (List.IsChain R ((a::xs)++[a]) ↔ List.IsChain R ((b::ys)++[b])) ∧
      prescribedOrderedPathEdges ((a::xs)++[a])=prescribedOrderedPathEdges ((b::ys)++[b]) ∧
      prescribedDirectedPathEdges ((a::xs)++[a])=prescribedDirectedPathEdges ((b::ys)++[b]) := by
  obtain ⟨pre,post,hxs,hleft,hright,hinter,hphys,hdir⟩:=prescribed_cycle_two_boundary_split a b xs
    (List.nodup_cons.mp hnodup).1 (List.nodup_cons.mp hnodup).2 hb
  let ys:=post++a::pre
  have hperm:(a::xs).Perm (b::ys):=by
    simpa [ys,hxs,List.cons_append,List.append_assoc] using
      (List.perm_append_comm (l₁:=a::pre) (l₂:=b::post))
  have hnodup':(b::ys).Nodup:=(hperm.nodup_iff).mp hnodup
  have hsets:(a::xs).toFinset=(b::ys).toFinset:=by
    ext x
    simp only [List.mem_toFinset]
    exact hperm.mem_iff
  have hp1:List.IsChain R ((a::xs)++[a]) ↔
      List.IsChain R (a::pre++[b]) ∧ List.IsChain R (b::post++[a]):=by
    simpa [hxs,List.cons_append,List.append_assoc] using
      (List.isChain_split (R:=R) (c:=b) (l₁:=a::pre) (l₂:=post++[a]))
  have hp2:List.IsChain R ((b::ys)++[b]) ↔
      List.IsChain R (b::post++[a]) ∧ List.IsChain R (a::pre++[b]):=by
    simpa [ys,List.cons_append,List.append_assoc] using
      (List.isChain_split (R:=R) (c:=a) (l₁:=b::post) (l₂:=pre++[b]))
  have hphys':prescribedOrderedPathEdges ((b::ys)++[b])=
      prescribedOrderedPathEdges (b::post++[a]) ∪ prescribedOrderedPathEdges (a::pre++[b]):=by
    simpa [ys,List.cons_append,List.append_assoc] using prescribed_path_edges_pivot a (pre++[b]) (b::post)
  have hdir':prescribedDirectedPathEdges ((b::ys)++[b])=
      prescribedDirectedPathEdges (b::post++[a]) ∪ prescribedDirectedPathEdges (a::pre++[b]):=by
    simpa [ys,List.cons_append,List.append_assoc] using prescribed_directed_path_edges_pivot a (pre++[b]) (b::post)
  refine ⟨ys,hnodup',hperm.length_eq,hsets,?_,?_,?_⟩
  · exact hp1.trans (and_comm.trans hp2.symm)
  · rw [hphys,hphys',Finset.union_comm]
  · rw [hdir,hdir',Finset.union_comm]
end Oberwolfach
