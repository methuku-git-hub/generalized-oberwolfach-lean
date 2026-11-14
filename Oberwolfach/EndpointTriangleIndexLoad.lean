module

public import Oberwolfach.EndpointTriangleCoordinates

@[expose] public section

/-! At a fixed index, the actual triangles are in bijection with their
unordered row edges. Each such edge contributes exactly one coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
  {Q F : SimpleGraph V} {S T : Finset V}

structure EndpointIndexEdge (Q F : SimpleGraph V) (S : Finset V) (u : V) (e : Sym2 V) : Prop where
  rows_mem : ∀ v∈e,v∈S
  row_edge : e∈Q.edgeSet
  row_allowed : e∉F.edgeSet
  spokes : ∀ v∈e,Q.Adj u v
  spoke_allowed : ∀ v∈e,¬F.Adj u v

theorem endpoint_triangle_index_coordinates_equiv (hST : Disjoint S T) (u : V) (hu : u∈T) :
    ∃ e : {C : EndpointTriangle Q F S T // u∈C.val}≃{edge : Sym2 V // EndpointIndexEdge Q F S u edge},
      ∀ C,endpointTriangleRowEdge C.val=(e C).val := by
  have hindex (C : {C : EndpointTriangle Q F S T // u∈C.val}) : endpointTriangleIndex C.val=u := by
    have hh : u∈C.val.val∩T:=Finset.mem_inter.mpr ⟨C.property,hu⟩
    rw [endpointTriangleIndex_spec] at hh
    exact (Finset.mem_singleton.mp hh).symm
  have hvalid (C : {C : EndpointTriangle Q F S T // u∈C.val}) :
      EndpointIndexEdge Q F S u (endpointTriangleRowEdge C.val) := by
    have hr:=endpointTriangleRowEdge_in_graph C.val
    refine ⟨fun v hv=>((endpointTriangleRowEdge_mem C.val v).mp hv).2,hr.1,hr.2,?_,?_⟩
    · intro v hv
      have hh:=(endpointTriangleRowEdge_mem C.val v).mp hv
      have hne : u≠v := by rintro rfl;exact Finset.disjoint_left.mp hST hh.2 hu
      exact C.val.property.2.2.2.1 u C.property v hh.1 hne
    · intro v hv
      exact C.val.property.2.2.2.2 u C.property v ((endpointTriangleRowEdge_mem C.val v).mp hv).1
  let f : {C : EndpointTriangle Q F S T // u∈C.val}→{edge : Sym2 V // EndpointIndexEdge Q F S u edge}:=
    fun C=>⟨endpointTriangleRowEdge C.val,hvalid C⟩
  have hf : Function.Bijective f := by
    constructor
    · intro C D h
      apply Subtype.ext
      apply endpointTriangle_coordinates_injective
      exact Prod.ext ((hindex C).trans (hindex D).symm) (congrArg Subtype.val h)
    · rintro ⟨edge,hedge⟩
      induction edge using Sym2.ind with
      | _ v w =>
        have hvS:=hedge.rows_mem v (by simp)
        have hwS:=hedge.rows_mem w (by simp)
        have hvwQ : Q.Adj v w:=hedge.row_edge
        have hvwF : ¬F.Adj v w:=hedge.row_allowed
        obtain ⟨C,hC⟩:=endpoint_triangle_from_vertices Q F S T hST u v w hu hvS hwS hvwQ.ne
          (hedge.spokes v (by simp)) (hedge.spokes w (by simp)) hvwQ
          (hedge.spoke_allowed v (by simp)) (hedge.spoke_allowed w (by simp)) hvwF
        change C.val={u,v,w} at hC
        let D : {C : EndpointTriangle Q F S T // u∈C.val}:=⟨C,by rw [hC];simp⟩
        refine ⟨D,Subtype.ext ?_⟩
        exact (endpointTriangle_coordinates_of_vertices hST C u v w hu hvS hwS hC).2
  exact ⟨Equiv.ofBijective f hf,fun _=>rfl⟩

theorem endpoint_triangle_index_load (hST : Disjoint S T) (u : V) (hu : u∈T)
    (weight : Sym2 V→ℝ) :
    (∑ C : EndpointTriangle Q F S T,if u∈C.val then weight (endpointTriangleRowEdge C) else 0)=
      ∑ edge : Sym2 V,if EndpointIndexEdge Q F S u edge then weight edge else 0 := by
  obtain ⟨e,he⟩:=endpoint_triangle_index_coordinates_equiv hST u hu
  have hl : (∑ C : EndpointTriangle Q F S T,if u∈C.val then weight (endpointTriangleRowEdge C) else 0)=
      ∑ C : {C : EndpointTriangle Q F S T // u∈C.val},weight (endpointTriangleRowEdge C.val) := by
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype _ (fun _=>by simp) _
  have hr : (∑ edge : Sym2 V,if EndpointIndexEdge Q F S u edge then weight edge else 0)=
      ∑ edge : {edge : Sym2 V // EndpointIndexEdge Q F S u edge},weight edge.val := by
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype _ (fun _=>by simp) _
  rw [hl,hr,←e.sum_comp (fun edge=>weight edge.val)]
  apply Finset.sum_congr rfl
  intro C hC
  rw [he C]

end Oberwolfach
