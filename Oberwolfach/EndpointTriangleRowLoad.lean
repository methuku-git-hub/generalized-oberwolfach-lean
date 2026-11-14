module

public import Oberwolfach.EndpointTriangleCoordinates

@[expose] public section

/-! Exact endpoint loads: at a fixed row vertex the other row and the
index determine one actual triangle. No orientation multiplicity remains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
  {Q F : SimpleGraph V} {S T : Finset V}

structure EndpointRowPair (Q F : SimpleGraph V) (S T : Finset V) (v : V) (p : V×V) : Prop where
  index_mem : p.1∈T
  other_mem : p.2∈S
  distinct : v≠p.2
  row_adj : Q.Adj v p.2
  first_spoke : Q.Adj p.1 v
  second_spoke : Q.Adj p.1 p.2
  row_allowed : ¬F.Adj v p.2
  first_allowed : ¬F.Adj p.1 v
  second_allowed : ¬F.Adj p.1 p.2

theorem endpoint_triangle_row_coordinates_equiv (hST : Disjoint S T) (v : V) (hv : v∈S) :
    ∃ e : {C : EndpointTriangle Q F S T // v∈C.val}≃{p : V×V // EndpointRowPair Q F S T v p},
      ∀ C,endpointTriangleRowEdge C.val=s(v,(e C).val.2) ∧ endpointTriangleIndex C.val=(e C).val.1 := by
  let other (C : {C : EndpointTriangle Q F S T // v∈C.val}) : V :=
    Classical.choose (endpointTriangle_fixed_row_coordinates hST C.val v hv C.property)
  have ho (C : {C : EndpointTriangle Q F S T // v∈C.val}) :
      v≠other C ∧ other C∈S ∧ endpointTriangleRowEdge C.val=s(v,other C) ∧
      C.val.val={endpointTriangleIndex C.val,v,other C} :=
    Classical.choose_spec (endpointTriangle_fixed_row_coordinates hST C.val v hv C.property)
  have hvalid (C : {C : EndpointTriangle Q F S T // v∈C.val}) :
      EndpointRowPair Q F S T v (endpointTriangleIndex C.val,other C) := by
    have hu:=endpointTriangleIndex_mem C.val
    have hw : other C∈C.val.val := by rw [(ho C).2.2.2];simp
    have huv : endpointTriangleIndex C.val≠v := by
      rintro he;rw [he] at hu;exact Finset.disjoint_left.mp hST hv hu.2
    have huw : endpointTriangleIndex C.val≠other C := by
      rintro he;rw [he] at hu;exact Finset.disjoint_left.mp hST (ho C).2.1 hu.2
    exact ⟨hu.2,(ho C).2.1,(ho C).1,
      C.val.property.2.2.2.1 v C.property _ hw (ho C).1,
      C.val.property.2.2.2.1 _ hu.1 v C.property huv,
      C.val.property.2.2.2.1 _ hu.1 _ hw huw,
      C.val.property.2.2.2.2 v C.property _ hw,
      C.val.property.2.2.2.2 _ hu.1 v C.property,
      C.val.property.2.2.2.2 _ hu.1 _ hw⟩
  let f : {C : EndpointTriangle Q F S T // v∈C.val}→{p : V×V // EndpointRowPair Q F S T v p} :=
    fun C=>⟨(endpointTriangleIndex C.val,other C),hvalid C⟩
  have hf : Function.Bijective f := by
    constructor
    · intro C D he
      have hpair : (endpointTriangleIndex C.val,other C)=(endpointTriangleIndex D.val,other D):=congrArg Subtype.val he
      apply Subtype.ext
      apply endpointTriangle_coordinates_injective
      change (endpointTriangleIndex C.val,endpointTriangleRowEdge C.val)=
        (endpointTriangleIndex D.val,endpointTriangleRowEdge D.val)
      apply Prod.ext
      · have hi : endpointTriangleIndex C.val=endpointTriangleIndex D.val:=congrArg Prod.fst hpair
        exact hi
      · rw [(ho C).2.2.1,(ho D).2.2.1]
        have hother : other C=other D:=congrArg Prod.snd hpair
        rw [hother]
    · intro p
      obtain ⟨C,hC⟩:=endpoint_triangle_from_vertices Q F S T hST p.val.1 v p.val.2
        p.property.index_mem hv p.property.other_mem p.property.distinct
        p.property.first_spoke p.property.second_spoke p.property.row_adj
        p.property.first_allowed p.property.second_allowed p.property.row_allowed
      change C.val={p.val.1,v,p.val.2} at hC
      let D : {C : EndpointTriangle Q F S T // v∈C.val}:=⟨C,by rw [hC];simp⟩
      have hc:=endpointTriangle_coordinates_of_vertices hST C p.val.1 v p.val.2
        p.property.index_mem hv p.property.other_mem hC
      refine ⟨D,Subtype.ext (Prod.ext hc.1 ?_)⟩
      have he : s(v,other D)=s(v,p.val.2):=(ho D).2.2.1.symm.trans hc.2
      rcases Sym2.eq_iff.mp he with ⟨_,h⟩|⟨h,_⟩
      · exact h
      · exact (p.property.distinct h).elim
  refine ⟨Equiv.ofBijective f hf,?_⟩
  intro C
  exact ⟨(ho C).2.2.1,rfl⟩

theorem endpoint_triangle_row_load (hST : Disjoint S T) (v : V) (hv : v∈S)
    (weight : Sym2 V→ℝ) :
    (∑ C : EndpointTriangle Q F S T,if v∈C.val then weight (endpointTriangleRowEdge C) else 0)=
      ∑ p : V×V,if EndpointRowPair Q F S T v p then weight s(v,p.2) else 0 := by
  obtain ⟨e,he⟩:=endpoint_triangle_row_coordinates_equiv hST v hv
  have hl : (∑ C : EndpointTriangle Q F S T,if v∈C.val then weight (endpointTriangleRowEdge C) else 0)=
      ∑ C : {C : EndpointTriangle Q F S T // v∈C.val},weight (endpointTriangleRowEdge C.val) := by
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype _ (fun _=>by simp) _
  have hr : (∑ p : V×V,if EndpointRowPair Q F S T v p then weight s(v,p.2) else 0)=
      ∑ p : {p : V×V // EndpointRowPair Q F S T v p},weight s(v,p.val.2) := by
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype _ (fun _=>by simp) _
  rw [hl,hr,←e.sum_comp (fun p=>weight s(v,p.val.2))]
  apply Finset.sum_congr rfl
  intro C hC
  rw [(he C).1]

end Oberwolfach
