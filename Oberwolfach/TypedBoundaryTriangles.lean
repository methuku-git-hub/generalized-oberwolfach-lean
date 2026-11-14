module

public import Oberwolfach.EndpointTriangleCoordinates
public import Oberwolfach.PhysicalTriangleWheels

@[expose] public section

/-! Interpret the selected endpoint records in the actual rim/hub parts.
An endpoint triangle contains exactly two rim vertices and one hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem typed_endpoint_triangle (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (C:EndpointTriangle (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      (A.image Sum.inl) (B.image Sum.inr)):
    ∃ v w:V,∃ u:U,v∈A∧w∈A∧u∈B∧v≠w∧
      C.val={Sum.inl v,Sum.inl w,Sum.inr u}∧Q.Adj v w∧H v u∧H w u∧¬F.Adj v w:=by
  obtain ⟨v',w',hne,hvw⟩:=Finset.card_eq_two.mp C.property.2.1
  have hv':v'∈C.val∩A.image Sum.inl:=by rw [hvw];simp
  have hw':w'∈C.val∩A.image Sum.inl:=by rw [hvw];simp
  obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp (Finset.mem_inter.mp hv').2
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp (Finset.mem_inter.mp hw').2
  obtain ⟨u,hu,huid⟩:=Finset.mem_image.mp (endpointTriangleIndex_mem C).2
  have hC:C.val={Sum.inl v,Sum.inl w,Sum.inr u}:=by
    have he:=endpointTriangle_vertices_coordinates C
    rw [(endpointTriangleRowEdge_spec C).2,hvw,←huid] at he
    exact he.trans (by ext a;simp only [Finset.mem_insert,Finset.mem_singleton];tauto)
  have hvC:Sum.inl v∈C.val:=(Finset.mem_inter.mp hv').1
  have hwC:Sum.inl w∈C.val:=(Finset.mem_inter.mp hw').1
  have huC:Sum.inr u∈C.val:=huid ▸ (endpointTriangleIndex_mem C).1
  refine ⟨v,w,u,hv,hw,hu,fun he=>hne (congrArg Sum.inl he),hC,
    C.property.2.2.2.1 _ hvC _ hwC hne,
    C.property.2.2.2.1 _ hvC _ huC (by simp),
    C.property.2.2.2.1 _ hwC _ huC (by simp),
    C.property.2.2.2.2 _ hvC _ hwC⟩

theorem endpoint_triangle_complete_at_row (Q F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (B:Finset U) (x:V) (hx:x∉A)
    (hQ:∀ v∈A,Q.Adj x v) (hH:∀ u∈B,H x u) (hF:∀ v∈A,¬F.Adj x v)
    (C:EndpointTriangle (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      (A.image Sum.inl) (B.image Sum.inr)):
    ∃ W:OrdinaryWheel Q F H 3,
      ordinaryWheelPhysicalGraph W=spanningRestriction ⊤ (insert (Sum.inl x) C.val) ∧
      (∀ a∈(ordinaryWheelRim W).support,a=x∨a∈A) ∧ ordinaryWheelHub W∈B:=by
  obtain ⟨v,w,u,hv,hw,hu,hvw,hC,hQvw,hHvu,hHwu,hFvw⟩:=typed_endpoint_triangle Q F H A B C
  have hxv:x≠v:=fun he=>hx (he.symm ▸ hv)
  have hxw:x≠w:=fun he=>hx (he.symm ▸ hw)
  have hcard:({x,v,w}:Finset V).card=3:=by simp [hxv,hxw,hvw]
  have hrim:∀ a∈({x,v,w}:Finset V),∀ b∈({x,v,w}:Finset V),a≠b→Q.Adj a b:=by
    intro a ha b hb hab
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl
    all_goals first | exact (hab rfl).elim | exact hQ _ hv | exact hQ _ hw | exact (hQ _ hv).symm | exact (hQ _ hw).symm | exact hQvw | exact hQvw.symm
  have hspoke:∀ a∈({x,v,w}:Finset V),H a u:=by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl
    · exact hH u hu
    · exact hHvu
    · exact hHwu
  have hconf:∀ a∈({x,v,w}:Finset V),∀ b∈({x,v,w}:Finset V),¬F.Adj a b:=by
    intro a ha b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl
    all_goals first | exact fun h=>h.ne rfl | exact hF _ hv | exact hF _ hw | exact fun h=>hF _ hv h.symm | exact fun h=>hF _ hw h.symm | exact hFvw | exact fun h=>hFvw h.symm
  have hclique:∀ a∈({x,v,w}:Finset V).image Sum.inl∪{Sum.inr u},
      ∀ b∈({x,v,w}:Finset V).image Sum.inl∪{Sum.inr u},a≠b→(ordinaryPhysicalGraph Q H).Adj a b:=by
    intro a ha b hb hab
    cases a with
    | inl a=>
      have ha':a∈({x,v,w}:Finset V):=by simpa using ha
      cases b with
      | inl b=>
        have hb':b∈({x,v,w}:Finset V):=by simpa using hb
        exact hrim a ha' b hb' (fun h=>hab (congrArg Sum.inl h))
      | inr b=>
        have hb':b=u:=by simpa using hb
        subst b;exact hspoke a ha'
    | inr a=>
      have ha':a=u:=by simpa using ha
      subst a
      cases b with
      | inl b=>
        have hb':b∈({x,v,w}:Finset V):=by simpa using hb
        exact hspoke b hb'
      | inr b=>
        have hb':b=u:=by simpa using hb
        exact (hab (congrArg Sum.inr hb'.symm)).elim
  obtain ⟨W,hWr,hWu,hW⟩:=physical_triangle_wheel Q F H {x,v,w} u hcard hclique hconf
  refine ⟨W,?_,?_,hWu.symm ▸ hu⟩
  · rw [hW,hC]
    congr 1
    ext a
    simp only [Finset.mem_union,Finset.mem_image,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro (⟨a,(rfl|rfl|rfl),rfl⟩|rfl) <;> tauto
    · rintro (rfl|rfl|rfl|rfl)
      · exact Or.inl ⟨x,Or.inl rfl,rfl⟩
      · exact Or.inl ⟨v,Or.inr (Or.inl rfl),rfl⟩
      · exact Or.inl ⟨w,Or.inr (Or.inr rfl),rfl⟩
      · exact Or.inr rfl
  · intro a ha
    have ha':a∈({x,v,w}:Finset V):=hWr ▸ Set.mem_toFinset.mpr ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha'
    rcases ha' with rfl|rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr hv
    · exact Or.inr hw

end Oberwolfach
