module

public import Oberwolfach.ActualRestrictedEdgeCover

@[expose] public section
/-! Directed complement arcs stay in the chosen host when both the old and
new parts respect that host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_restricted_directed_arcs_in_host
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2)
    (data:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (D:Finset X) (finalEdges:Finset (Sym2 X))
    (hFinal:∀e∈finalEdges,∃x∈e.toFinset,x∈D)
    (fC:{x // x∉D}↪V) (ψ:X→V) (Φ:{x // x∈data.remaining}→V)
    (hold:∀(x:{x // x∉D}),x.val∈data.oldDomain→fC x=ψ x.val)
    (hnew:∀(x:{x // x∉D}) (hx:x.val∈data.remaining),fC x=Φ ⟨x.val,hx⟩)
    (Dsrc:X→X→Prop) (Dhost:V→V→Prop)
    (hOldArc:∀x y,s(x,y)∈data.deletedEdges\finalEdges→Dsrc x y→Dhost (ψ x) (ψ y))
    (hNewArc:∀x y:{x // x∈data.remaining},Dsrc x.1 y.1→data.graph.Adj x.1 y.1→Dhost (Φ x) (Φ y)):
    ∀x y:{x // x∉D},F.Adj x.1 y.1→Dsrc x.1 y.1→Dhost (fC x) (fC y):=by
  intro x y hFxy hSrc
  have hNotFinal:s(x.1,y.1)∉finalEdges:=by
    intro he
    obtain ⟨z,hz,hzD⟩:=hFinal s(x.1,y.1) he
    have hz':z=x.1 ∨ z=y.1:=by simpa using hz
    rcases hz' with rfl|rfl
    · exact x.2 hzD
    · exact y.2 hzD
  by_cases hDel:s(x.1,y.1)∈data.deletedEdges
  · have hx:x.1∈data.oldDomain:=data.deleted_edge_vertices_in_old_domain hCycle _ hDel x.1 (by simp)
    have hy:y.1∈data.oldDomain:=data.deleted_edge_vertices_in_old_domain hCycle _ hDel y.1 (by simp)
    rw [hold x hx,hold y hy]
    exact hOldArc x.1 y.1 (Finset.mem_sdiff.mpr ⟨hDel,hNotFinal⟩) hSrc
  · have hGraph:data.graph.Adj x.1 y.1:=by
      change (F.deleteEdges (↑data.deletedEdges:Set (Sym2 X))).Adj x.1 y.1
      exact SimpleGraph.deleteEdges_adj.mpr ⟨hFxy,hDel⟩
    have hIso:∀z,z∉data.remaining→∀w,¬data.graph.Adj z w:=(data.graph_facts hF).2.2.2.2.1
    have hx:x.1∈data.remaining:=by by_contra h;exact hIso _ h _ hGraph
    have hy:y.1∈data.remaining:=by by_contra h;exact hIso _ h _ hGraph.symm
    rw [hnew x hx,hnew y hy]
    exact hNewArc ⟨x.1,hx⟩ ⟨y.1,hy⟩ hSrc hGraph
end Oberwolfach
