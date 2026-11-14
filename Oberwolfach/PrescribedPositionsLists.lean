module

public import Oberwolfach.PrescribedPositionOriginalSelection
public import Oberwolfach.PrescribedPositionInducedArcs
public import Oberwolfach.PrescribedPositionPairing

@[expose] public section
/-! Prescribe an oriented matching and isolated images using explicit lists
of target matching arcs and singleton labels. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_positions_from_lists (Q:SimpleGraph X) (D:X→X→Prop)
    (hdeg:∀x,Q.degree x≤2) (hrep:∀x y,Q.Adj x y→D x y ∨ D y x)
    (hDQ:∀x y,D x y→Q.Adj x y) (horiented:∀x y,D x y→¬D y x)
    (A:Finset X) (hA:∀x∈A,∀y∈A,¬Q.Adj x y) (f:X→V) (hinj:Set.InjOn f (↑A:Set X))
    (ms:List (V×V)) (zs:List V)
    (hM:(ms.flatMap prescribedPairVertices).Nodup) (hZ:zs.Nodup)
    (hMZ:List.Disjoint (ms.flatMap prescribedPairVertices) zs)
    (hOld:Disjoint (A.image f) (ms.flatMap prescribedPairVertices++zs).toFinset)
    (hedges:Fintype.card X≤Q.edgeFinset.card+A.card)
    (hsize:8*A.card+8*ms.length+4*zs.length+10≤Fintype.card X):
    ∃ (B:Finset X) (g:X→V),A⊆B ∧ Set.InjOn g (↑B:Set X) ∧ (∀x∈A,g x=f x) ∧
      B.image g=A.image f∪(ms.flatMap prescribedPairVertices).toFinset∪zs.toFinset ∧
      (prescribedInducedArcs D B).image (Prod.map g g)=ms.toFinset := by
  obtain ⟨es,vs,heslen,hvslen,he,hpair,hvs,hcross,hsingle,hnodup⟩:=
    prescribed_position_selection_original Q D hdeg hrep A ms.length zs.length hedges hsize
  have htarget:(ms.flatMap prescribedPairVertices++zs).Nodup:=List.nodup_append'.mpr ⟨hM,hZ,hMZ⟩
  have hdisS:∀ x∈es.flatMap prescribedPairVertices++vs,x∉A:=by
    intro x hx
    have hout:x∉prescribedClosedNeighbourhoods Q A:=by
      rcases List.mem_append.mp hx with hx|hx
      · obtain ⟨e,he',hx⟩:=List.mem_flatMap.mp hx
        simp only [prescribedPairVertices,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with hx|hx
        · subst x;exact (he e he').2.2.1
        · subst x;exact (he e he').2.2.2
      · exact hvs x hx
    exact (prescribed_outside_closed_neighbourhood Q A x hout).1
  have hdisT:∀ y∈ms.flatMap prescribedPairVertices++zs,y∉A.image f:=by
    intro y hy hOldY
    exact (Finset.disjoint_left.mp hOld hOldY) (List.mem_toFinset.mpr hy)
  have hsel:∀e∈es,D e.1 e.2:=by intro e he';exact (he e he').1
  have he':∀e∈es,D e.1 e.2 ∧ e.1∉prescribedClosedNeighbourhoods Q A ∧ e.2∉prescribedClosedNeighbourhoods Q A:=by
    intro e he';exact ⟨(he e he').1,(he e he').2.2.1,(he e he').2.2.2⟩
  have honly:=prescribed_selected_induced_arcs Q D A hDQ horiented hA es vs he' hpair hvs hcross hsingle
  let B:=A∪(es.flatMap prescribedPairVertices++vs).toFinset
  obtain ⟨g,hginj,hgpres,hgimage,hgarcs⟩:=prescribed_position_pairing D A f hinj es ms vs zs
    heslen hvslen hnodup htarget hdisS hdisT hsel honly
  refine ⟨B,g,Finset.subset_union_left,hginj,hgpres,?_,hgarcs⟩
  simpa [B,List.toFinset_append,Finset.union_assoc] using hgimage
end Oberwolfach
