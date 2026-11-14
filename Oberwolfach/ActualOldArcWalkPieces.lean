module

public import Oberwolfach.ActualOldDirectedArcsFromWalks
public import Oberwolfach.ResidualActualData
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

@[expose] public section
/-! The non-final old edges are exactly covered by selected source cycles and
selected runs, so directed target walks supply their host arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem directed_arc_from_walk_edge
    {X V:Type} [DecidableEq X] [DecidableEq V] (G:SimpleGraph X)
    (σ:X→X) (D:X→X→Prop) (ψ:X→V) (H:Finset (V×V))
    (halign:∀x,D x (σ x)) (hunique:∀x y z,D x y→D x z→y=z)
    (hno2:∀x,σ (σ x)≠x) {u v:X} (p:G.Walk u v)
    (hstep:∀j<p.length,σ (p.getVert j)=p.getVert (j+1))
    (htarget:∀j<p.length,(ψ (p.getVert j),ψ (p.getVert (j+1)))∈H):
    ∀x y,s(x,y)∈p.edges.toFinset→D x y→(ψ x,ψ y)∈H:=by
  intro x y he hxy
  obtain ⟨j,hj,heq⟩:=(p.mk_mem_edges_iff_exists).mp (List.mem_toFinset.mp he)
  have hy:σ x=y:=hunique x (σ x) y (halign x) hxy
  rcases Sym2.eq_iff.mp heq with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simpa only [←ha,←hb] using htarget j hj
  · have htwo:σ (σ (p.getVert j))=p.getVert j:=by
      rw [hstep j hj,hb,hy,←ha]
    exact False.elim (hno2 _ htwo)

theorem actual_old_arc_host_from_selected_walks
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop)
    (hpair:pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀p∈pieces,p.OriginalValid D)
    (hArcs:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces)
    (halign:∀x,D x (factorCycleOrientation G e x))
    (data:ActualResidualData (K:=K) (J:=J) G) (ψ:X→V) (H:Finset (V×V))
    (hcycleStep:∀j∈data.t,∀k<(data.C j).length,
      factorCycleOrientation G e ((data.C j).getVert k)=(data.C j).getVert (k+1))
    (hcycleTarget:∀j∈data.t,∀k<(data.C j).length,
      (ψ ((data.C j).getVert k),ψ ((data.C j).getVert (k+1)))∈H)
    (hrunStep:∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      factorCycleOrientation G e ((data.path (.inr r)).getVert k)=(data.path (.inr r)).getVert (k+1))
    (hrunTarget:∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      (ψ ((data.path (.inr r)).getVert k),ψ ((data.path (.inr r)).getVert (k+1)))∈H):
    ∀x y,s(x,y)∈data.deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))→
      D x y→(ψ x,ψ y)∈H:=by
  intro x y he hxy
  have hu:=actual_source_orientation_has_unique_outgoing pieces D hpair hvalid hArcs
  have hn:=factor_orientation_no_two_cycles G hG e
  obtain ⟨he,hnfinal⟩:=Finset.mem_sdiff.mp he
  rcases Finset.mem_union.mp he with hc | hp
  · obtain ⟨j,hj,hje⟩:=Finset.mem_biUnion.mp hc
    exact directed_arc_from_walk_edge G (factorCycleOrientation G e) D ψ H halign hu hn (data.C j)
      (hcycleStep j hj) (hcycleTarget j hj) x y hje hxy
  · obtain ⟨z,_,hze⟩:=Finset.mem_biUnion.mp hp
    cases z with
    | inl i =>
      exact False.elim (hnfinal (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hze⟩))
    | inr r =>
      exact directed_arc_from_walk_edge G (factorCycleOrientation G e) D ψ H halign hu hn (data.path (.inr r))
        (hrunStep r) (hrunTarget r) x y hze hxy
end Oberwolfach
