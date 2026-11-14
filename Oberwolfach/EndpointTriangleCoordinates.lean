module

public import Oberwolfach.EndpointTriangles

@[expose] public section

/-! An endpoint triangle has a unique index and a unique unordered row
edge. These coordinates identify the actual triangle without choosing an
orientation of its row edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
  {Q F : SimpleGraph V} {S T : Finset V}

def endpointTriangleIndex (C : EndpointTriangle Q F S T) : V :=
  Classical.choose (Finset.card_eq_one.mp C.property.2.2.1)

theorem endpointTriangleIndex_spec (C : EndpointTriangle Q F S T) :
    C.val∩T={endpointTriangleIndex C} :=
  Classical.choose_spec (Finset.card_eq_one.mp C.property.2.2.1)

theorem endpointTriangleRowEdge_exists (C : EndpointTriangle Q F S T) :
    ∃ e : Sym2 V,¬e.IsDiag ∧ e.toFinset=C.val∩S := by
  obtain ⟨v,w,hne,he⟩:=Finset.card_eq_two.mp C.property.2.1
  refine ⟨s(v,w),?_,?_⟩
  · simpa using hne
  · rw [Sym2.toFinset_mk_eq,he]

def endpointTriangleRowEdge (C : EndpointTriangle Q F S T) : Sym2 V :=
  Classical.choose (endpointTriangleRowEdge_exists C)

theorem endpointTriangleRowEdge_spec (C : EndpointTriangle Q F S T) :
    ¬(endpointTriangleRowEdge C).IsDiag ∧ (endpointTriangleRowEdge C).toFinset=C.val∩S :=
  Classical.choose_spec (endpointTriangleRowEdge_exists C)

theorem endpointTriangleIndex_mem (C : EndpointTriangle Q F S T) :
    endpointTriangleIndex C∈C.val ∧ endpointTriangleIndex C∈T := by
  apply Finset.mem_inter.mp
  rw [endpointTriangleIndex_spec]
  exact Finset.mem_singleton_self _

theorem endpointTriangleRowEdge_mem (C : EndpointTriangle Q F S T) (v : V) :
    v∈endpointTriangleRowEdge C ↔ v∈C.val ∧ v∈S := by
  rw [←Sym2.mem_toFinset,(endpointTriangleRowEdge_spec C).2,Finset.mem_inter]

theorem endpointTriangle_vertices_coordinates (C : EndpointTriangle Q F S T) :
    C.val=insert (endpointTriangleIndex C) (endpointTriangleRowEdge C).toFinset := by
  rw [(endpointTriangleRowEdge_spec C).2]
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp (C.property.1 hv) with hS|hT
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hv,hS⟩)
    · have hh : v∈C.val∩T:=Finset.mem_inter.mpr ⟨hv,hT⟩
      rw [endpointTriangleIndex_spec] at hh
      exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hh))
  · intro hv
    rcases Finset.mem_insert.mp hv with rfl|hv
    · exact (endpointTriangleIndex_mem C).1
    · exact (Finset.mem_inter.mp hv).1

theorem endpointTriangle_coordinates_injective :
    Function.Injective (fun C : EndpointTriangle Q F S T=>(endpointTriangleIndex C,endpointTriangleRowEdge C)) := by
  intro C D h
  have hi : endpointTriangleIndex C=endpointTriangleIndex D:=congrArg Prod.fst h
  have he : endpointTriangleRowEdge C=endpointTriangleRowEdge D:=congrArg Prod.snd h
  apply Subtype.ext
  rw [endpointTriangle_vertices_coordinates C,endpointTriangle_vertices_coordinates D,hi,he]

theorem endpointTriangleRowEdge_in_graph (C : EndpointTriangle Q F S T) :
    endpointTriangleRowEdge C∈Q.edgeSet ∧ endpointTriangleRowEdge C∉F.edgeSet := by
  generalize he : endpointTriangleRowEdge C=e
  induction e using Sym2.ind with
  | _ v w =>
    have hv : v∈C.val := ((endpointTriangleRowEdge_mem C v).mp (by rw [he];simp)).1
    have hw : w∈C.val := ((endpointTriangleRowEdge_mem C w).mp (by rw [he];simp)).1
    have hne : v≠w := by simpa only [he,Sym2.mk_isDiag_iff] using (endpointTriangleRowEdge_spec C).1
    exact ⟨C.property.2.2.2.1 v hv w hw hne,C.property.2.2.2.2 v hv w hw⟩

theorem endpointTriangle_fixed_row_coordinates (hST : Disjoint S T)
    (C : EndpointTriangle Q F S T) (v : V) (hvS : v∈S) (hvC : v∈C.val) :
    ∃ w : V,v≠w ∧ w∈S ∧ endpointTriangleRowEdge C=s(v,w) ∧
      C.val={endpointTriangleIndex C,v,w} := by
  have hv := (endpointTriangleRowEdge_mem C v).mpr ⟨hvC,hvS⟩
  obtain ⟨w,he⟩:=Sym2.mem_iff_exists.mp hv
  have hw := ((endpointTriangleRowEdge_mem C w).mp (by rw [he];simp)).2
  have hne : v≠w := by simpa only [he,Sym2.mk_isDiag_iff] using (endpointTriangleRowEdge_spec C).1
  refine ⟨w,hne,hw,he,?_⟩
  rw [endpointTriangle_vertices_coordinates C,he,Sym2.toFinset_mk_eq]

theorem endpointTriangle_coordinates_of_vertices (hST : Disjoint S T)
    (C : EndpointTriangle Q F S T) (u v w : V) (hu : u∈T) (hv : v∈S) (hw : w∈S)
    (hC : C.val={u,v,w}) :
    endpointTriangleIndex C=u ∧ endpointTriangleRowEdge C=s(v,w) := by
  have huS : u∉S:=fun h=>Finset.disjoint_left.mp hST h hu
  have hvT : v∉T:=fun h=>Finset.disjoint_left.mp hST hv h
  have hwT : w∉T:=fun h=>Finset.disjoint_left.mp hST hw h
  have hT : C.val∩T={u} := by
    rw [hC,Finset.insert_inter_of_mem hu,Finset.insert_inter_of_notMem hvT]
    simp [hwT]
  have hS : C.val∩S={v,w} := by
    rw [hC,Finset.insert_inter_of_notMem huS,Finset.insert_inter_of_mem hv]
    simp [hw]
  constructor
  · have hh:=(endpointTriangleIndex_spec C).symm.trans hT
    exact Finset.singleton_injective hh
  · apply Sym2.ext
    intro z
    rw [←Sym2.mem_toFinset,←Sym2.mem_toFinset,(endpointTriangleRowEdge_spec C).2,hS,Sym2.toFinset_mk_eq]

end Oberwolfach
