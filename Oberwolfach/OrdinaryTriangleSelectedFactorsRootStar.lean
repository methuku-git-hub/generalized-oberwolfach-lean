module

public import Oberwolfach.OrdinaryTriangleSelectedFactors
public import Oberwolfach.OrdinaryDeepRootFreeFamilies

@[expose] public section
/-! If the actual boundary classes avoid the deeper vertices and hubs,
    their selected triangle factors automatically avoid the deep blocker. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_triangle_selected_factors_automatically_avoid_root_star
    (Q F:SimpleGraph V) (H:V→U→Prop) (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
    (limit:ℝ) (C:OrdinaryTriangleSelectedFactors Q F H A B T Y hAB limit)
    (Tdeep:Finset V) (Wdeep:Finset U)
    (hY:∀j,Disjoint (Y j) Tdeep) (hA:∀i,Disjoint (A i) Tdeep) (hB:∀i,Disjoint (B i) Wdeep):
    (∀j,Disjoint ((localOrdinaryFactorGraph (C.hub j)).map (Function.Embedding.inl:V↪V⊕U))
      (ordinaryDeepRootStar Tdeep Wdeep)) ∧
    (∀i,Disjoint (endpointFactorGraph (hAB i) (C.row i)) (ordinaryDeepRootStar Tdeep Wdeep)) :=by
  have hstar (x y:V⊕U) (h:(ordinaryDeepRootStar Tdeep Wdeep).Adj x y):
      x∈ordinaryInnerVertices Tdeep Wdeep ∨ y∈ordinaryInnerVertices Tdeep Wdeep:=by
    cases x with
    | inl v=>
      cases y with
      | inl w=>
        change (⊤:SimpleGraph V).Adj v w ∧ (v∈Tdeep ∨ w∈Tdeep) at h
        simpa only [ordinaryInnerVertices_left] using h.2
      | inr u=>
        change True ∧ (v∈Tdeep ∨ u∈Wdeep) at h
        simpa only [ordinaryInnerVertices_left,ordinaryInnerVertices_right] using h.2
    | inr u=>
      cases y with
      | inl v=>
        change True ∧ (v∈Tdeep ∨ u∈Wdeep) at h
        have hh:=h.2.symm
        simpa only [ordinaryInnerVertices_left,ordinaryInnerVertices_right] using hh
      | inr w=>cases h
  have hOutside (i:I) (x:V⊕U)
      (hx:x∈(A i).image Sum.inl∪(B i).image Sum.inr):x∉ordinaryInnerVertices Tdeep Wdeep:=by
    rcases Finset.mem_union.mp hx with ha|hb
    · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp ha
      intro hdeep
      exact Finset.disjoint_left.mp (hA i) hv ((ordinaryInnerVertices_left Tdeep Wdeep v).mp hdeep)
    · obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hb
      intro hdeep
      exact Finset.disjoint_left.mp (hB i) hu ((ordinaryInnerVertices_right Tdeep Wdeep u).mp hdeep)
  constructor
  · intro j
    apply disjoint_iff_inf_le.mpr
    intro x y hxy
    have hroot:=hstar x y hxy.2
    have hh:=hxy.1
    rw [graph_map_inl_physical] at hh
    cases x with
    | inl v=>
      cases y with
      | inl w=>
        change (localOrdinaryFactorGraph (C.hub j)).Adj v w at hh
        have hvw:=(spanningRestriction_adj _ _ _ _).mp
          (localOrdinaryFactorGraph_restriction (C.hub j) (Y j) (C.hub_cover j) hh)
        rcases hroot with hv|hw
        · exact Finset.disjoint_left.mp (hY j) hvw.2.1 ((ordinaryInnerVertices_left Tdeep Wdeep v).mp hv)
        · exact Finset.disjoint_left.mp (hY j) hvw.2.2 ((ordinaryInnerVertices_left Tdeep Wdeep w).mp hw)
      | inr u=>cases hh
    | inr u=>cases y <;> cases hh
  · intro i
    apply (endpointFactorGraph_choice (hAB i) (C.row i) ((A i).image Sum.inl∪(B i).image Sum.inr)
      (ordinaryDeepRootStar Tdeep Wdeep) (C.row_disjoint i) (C.row_cover i) ?_).2.2
    intro D hD x hx y hy hdeep
    have hxclass:x∈(A i).image Sum.inl∪(B i).image Sum.inr:=by
      rw [←C.row_cover i]
      exact Finset.mem_biUnion.mpr ⟨D,hD,hx⟩
    have hyclass:y∈(A i).image Sum.inl∪(B i).image Sum.inr:=by
      rw [←C.row_cover i]
      exact Finset.mem_biUnion.mpr ⟨D,hD,hy⟩
    exact (hstar x y hdeep).elim (hOutside i x hxclass) (hOutside i y hyclass)
end Oberwolfach
