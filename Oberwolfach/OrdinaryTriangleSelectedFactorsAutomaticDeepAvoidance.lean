module

public import Oberwolfach.OrdinaryTriangleSelectedFactors
public import Oberwolfach.OrdinaryDeepBlockerNested

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

theorem ordinary_triangle_selected_factors_automatically_avoid_deep
    (Q F:SimpleGraph V) (H:V→U→Prop) (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
    (limit:ℝ) (C:OrdinaryTriangleSelectedFactors Q F H A B T Y hAB limit)
    (Tdeep:Finset V) (Wdeep:Finset U)
    (hY:∀j,Disjoint (Y j) Tdeep) (hA:∀i,Disjoint (A i) Tdeep) (hB:∀i,Disjoint (B i) Wdeep):
    (∀j,Disjoint ((localOrdinaryFactorGraph (C.hub j)).map (Function.Embedding.inl:V↪V⊕U))
      (ordinaryDeepBlocker Tdeep Wdeep)) ∧
    (∀i,Disjoint (endpointFactorGraph (hAB i) (C.row i)) (ordinaryDeepBlocker Tdeep Wdeep)) :=by
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
    have hdeep: x∈ordinaryInnerVertices Tdeep Wdeep:=
      (ordinary_deep_blocker_support_nested Tdeep Tdeep Wdeep Wdeep (by intro v hv;exact hv) (by intro u hu;exact hu) x y hxy.2).1
    have hh:=hxy.1
    rw [graph_map_inl_physical] at hh
    cases x with
    | inl v=>
      cases y with
      | inl w=>
        change (localOrdinaryFactorGraph (C.hub j)).Adj v w at hh
        have hv: v∈Y j:=((spanningRestriction_adj _ _ _ _).mp
          (localOrdinaryFactorGraph_restriction (C.hub j) (Y j) (C.hub_cover j) hh)).2.1
        exact Finset.disjoint_left.mp (hY j) hv ((ordinaryInnerVertices_left Tdeep Wdeep v).mp hdeep)
      | inr u=>cases hh
    | inr u=>cases y <;> cases hh
  · intro i
    apply (endpointFactorGraph_choice (hAB i) (C.row i) ((A i).image Sum.inl∪(B i).image Sum.inr)
      (ordinaryDeepBlocker Tdeep Wdeep) (C.row_disjoint i) (C.row_cover i) ?_).2.2
    intro D hD x hx y hy hdeep
    have hxclass:x∈(A i).image Sum.inl∪(B i).image Sum.inr:=by
      rw [←C.row_cover i]
      exact Finset.mem_biUnion.mpr ⟨D,hD,hx⟩
    exact hOutside i x hxclass
      (ordinary_deep_blocker_support_nested Tdeep Tdeep Wdeep Wdeep (by intro v hv;exact hv) (by intro u hu;exact hu) x y hdeep).1
end Oberwolfach
