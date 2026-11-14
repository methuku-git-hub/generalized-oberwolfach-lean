module

public import Oberwolfach.OrdinaryReferenceSpokeNewEdgeCoverage
public import Oberwolfach.ResidualActualEdgePartition

@[expose] public section
/-! The coherent old images avoid the reserved layer; every lost reference
spoke is therefore charged to one of the bounded-degree new edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matched_reference_spoke_loss
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {X A B J:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,DecidableEq (A u)] [∀u,DecidableEq (B u)] [∀u,DecidableEq (J u)]
    (F:∀u,SimpleGraph (X u)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (data:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u) (F u))
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (ψ:∀u,X u→V) (f:∀u,X u↪V) (Href:V→U→Prop) (Reserve:U→Finset V)
    (hRef:∀u v,Href v u→v∈Reserve u)
    (hOldAvoid:∀u,Disjoint ((data u).oldDomain.image (ψ u)) (Reserve u))
    (hfold:∀u x,x∈(data u).oldDomain→f u x=ψ u x)
    (New:U→Finset (Sym2 V))
    (hpart:∀u,((F u).edgeFinset).image (Sym2.map (f u))=(data u).deletedEdges.image (Sym2.map (ψ u))∪New u)
    (hpair:PairwisePhysicalDisjoint New)
    (rowLoss colLoss:ℝ) (hdegree:∀v,((prescribedPhysicalUnion New).degree v:ℝ)≤rowLoss)
    (hsize:∀u,((data u).remaining.card:ℝ)≤colLoss):
    (∀v,((Finset.univ.filter (fun u=>Href v u ∧ v∈Set.range (f u))).card:ℝ)≤rowLoss) ∧
    (∀u,((Finset.univ.filter (fun v=>Href v u ∧ v∈Set.range (f u))).card:ℝ)≤colLoss) :=by
  have hOldPoint:∀u x,x∈(data u).oldDomain→¬Href (f u x) u:=by
    intro u x hx href
    have hm:ψ u x∈(data u).oldDomain.image (ψ u):=Finset.mem_image.mpr ⟨x,hx,rfl⟩
    have hr:ψ u x∈Reserve u:=hRef u (ψ u x) (by simpa only [hfold u x hx] using href)
    exact Finset.disjoint_left.mp (hOldAvoid u) hm hr
  have hOldEdge:∀u e,e∈(data u).deletedEdges.image (Sym2.map (ψ u))→∀v,v∈e.toFinset→¬Href v u:=by
    intro u e he v hv href
    obtain ⟨ed,hed,hmap⟩:=Finset.mem_image.mp he
    rw [←hmap] at hv
    induction ed using Sym2.inductionOn with
    | _ x y=>
      have hx:x∈(data u).oldDomain:=(data u).deleted_edge_vertices_in_old_domain (hCycle u) _ hed x (by simp)
      have hy:y∈(data u).oldDomain:=(data u).deleted_edge_vertices_in_old_domain (hCycle u) _ hed y (by simp)
      simp only [Sym2.map_mk,Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with hv|hv
      · subst v
        exact hOldPoint u x hx (by simpa only [hfold u x hx] using href)
      · subst v
        exact hOldPoint u y hy (by simpa only [hfold u y hy] using href)
  have hcover:=ordinary_reference_spoke_new_edge_coverage F hF f Href
    (fun u=>(data u).deletedEdges.image (Sym2.map (ψ u))) New hpart hOldEdge
  constructor
  · exact ordinary_reference_spoke_loss_from_new_edges f Href New hpair hcover rowLoss hdegree
  · exact ordinary_reference_spoke_column_loss_from_remaining f Href (fun u=>(data u).oldDomain)
      (fun u=>(data u).remaining) (fun u=>(data u).old_domain_union_remaining (hCycle u)) hOldPoint colLoss hsize
end Oberwolfach
