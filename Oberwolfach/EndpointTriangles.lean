module

public import Oberwolfach.OrdinaryLocalCycles
public import Oberwolfach.HubCycleProfiles

@[expose] public section

/-! Endpoint triangles are unordered three-vertex sets: two row vertices
and one index. The graph Q contains precisely the permitted row and spoke
edges in applications. Forbidden pairs are excluded inside each triangle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev EndpointTriangle (Q F : SimpleGraph V) (S T : Finset V) :=
  {X : Finset V // X⊆S∪T ∧ (X∩S).card=2 ∧ (X∩T).card=1 ∧
    (∀ x∈X,∀ y∈X,x≠y → Q.Adj x y) ∧ ∀ x∈X,∀ y∈X,¬F.Adj x y}

def endpointTriangleVertices {Q F : SimpleGraph V} {S T : Finset V}
    (C : EndpointTriangle Q F S T) : Finset V := C.val

theorem endpointTriangleVertices_card {Q F : SimpleGraph V} {S T : Finset V}
    (hST : Disjoint S T) (C : EndpointTriangle Q F S T) :
    (endpointTriangleVertices C).card=3 := by
  have hu : C.val=(C.val∩S)∪(C.val∩T) := by
    ext v
    simp only [Finset.mem_union,Finset.mem_inter]
    constructor
    · intro hv;exact (Finset.mem_union.mp (C.property.1 hv)).elim (fun h=>Or.inl ⟨hv,h⟩) (fun h=>Or.inr ⟨hv,h⟩)
    · tauto
  change C.val.card=3
  rw [hu,Finset.card_union_of_disjoint (hST.mono Finset.inter_subset_right Finset.inter_subset_right)]
  rw [C.property.2.1,C.property.2.2.1]

theorem endpointTriangle_multiplicity (Q F : SimpleGraph V) (S T Y : Finset V) :
    Fintype.card {C : EndpointTriangle Q F S T // endpointTriangleVertices C=Y}≤1 := by
  apply Fintype.card_le_one_iff.mpr
  intro C D
  apply Subtype.ext;apply Subtype.ext
  exact C.property.trans D.property.symm

theorem endpoint_triangle_from_tuple (Q F : SimpleGraph V) (S T : Finset V)
    (hST : Disjoint S T) (f : Fin 3→V) (hf : Function.Injective f)
    (hT : f 0∈T) (hS : ∀ j : Fin 2,f j.succ∈S)
    (hQ : ∀ i j,i≠j → Q.Adj (f i) (f j)) (hF : ∀ i j,¬F.Adj (f i) (f j)) :
    ∃ C : EndpointTriangle Q F S T,endpointTriangleVertices C=Finset.univ.image f := by
  let X := Finset.univ.image f
  have hzeroS : f 0∉S := fun h=>Finset.disjoint_left.mp hST h hT
  have hrowT (j : Fin 2) : f j.succ∉T := fun h=>Finset.disjoint_left.mp hST (hS j) h
  have hXS : X∩S=(Finset.univ.image (fun j : Fin 2=>f j.succ)) := by
    ext v
    simp only [X,Finset.mem_inter,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨i,rfl⟩,hi⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl|⟨j,rfl⟩
      · exact (hzeroS hi).elim
      · exact ⟨j,rfl⟩
    · rintro ⟨j,rfl⟩;exact ⟨⟨j.succ,rfl⟩,hS j⟩
  have hXT : X∩T={f 0} := by
    ext v
    simp only [X,Finset.mem_inter,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨i,rfl⟩,hi⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl|⟨j,rfl⟩
      · rfl
      · exact (hrowT j hi).elim
    · rintro rfl;exact ⟨⟨0,rfl⟩,hT⟩
  refine ⟨⟨X,?_,?_,?_,?_,?_⟩,rfl⟩
  · intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    rcases Fin.eq_zero_or_eq_succ i with rfl|⟨j,rfl⟩
    · exact Finset.mem_union_right _ hT
    · exact Finset.mem_union_left _ (hS j)
  · rw [hXS,Finset.card_image_of_injective _ (show Function.Injective (fun j : Fin 2=>f j.succ) from fun i j h=>(Fin.succ_injective 2) (hf h))]
    simp
  · rw [hXT];simp
  · intro v hv w hw hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
    exact hQ i j (fun h=>hne (congrArg f h))
  · intro v hv w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
    exact hF i j

end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem endpoint_triangle_from_vertices (Q F : SimpleGraph V) (S T : Finset V)
    (hST : Disjoint S T) (u v w : V) (hu : u∈T) (hv : v∈S) (hw : w∈S) (hvw : v≠w)
    (huvQ : Q.Adj u v) (huwQ : Q.Adj u w) (hvwQ : Q.Adj v w)
    (huvF : ¬F.Adj u v) (huwF : ¬F.Adj u w) (hvwF : ¬F.Adj v w) :
    ∃ C : EndpointTriangle Q F S T,endpointTriangleVertices C={u,v,w} := by
  have huv : u≠v := by rintro rfl;exact Finset.disjoint_left.mp hST hv hu
  have huw : u≠w := by rintro rfl;exact Finset.disjoint_left.mp hST hw hu
  have hvuQ := huvQ.symm
  have hwuQ := huwQ.symm
  have hwvQ := hvwQ.symm
  have hvuF : ¬F.Adj v u := fun h=>huvF h.symm
  have hwuF : ¬F.Adj w u := fun h=>huwF h.symm
  have hwvF : ¬F.Adj w v := fun h=>hvwF h.symm
  have hf : Function.Injective (![u,v,w] : Fin 3→V) := by
    intro i j he;fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨C,hC⟩ := endpoint_triangle_from_tuple Q F S T hST ![u,v,w] hf hu
    (by intro j;fin_cases j <;> simp_all)
    (by intro i j hij;fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i j;fin_cases i <;> fin_cases j <;> simp_all)
  refine ⟨C,hC.trans ?_⟩
  ext z
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨i,rfl⟩;fin_cases i <;> simp
  · rintro (rfl|rfl|rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

end Oberwolfach
