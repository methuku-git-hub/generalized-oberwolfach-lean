module

public import Oberwolfach.EndpointPotentialPredicates

@[expose] public section

/-! The source endpoint domain consists of the two classes and the row
root. A conflict graph supported on rows has no incident edges at indices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem endpoint_source_domain_card (A B : Finset V) (x : V)
    (hcover : ∀ v:V,v∈insert x (A∪B)) (hA : 0<A.card) (hBA : B.card≤A.card) :
    Fintype.card V≤3*A.card := by
  have hsub : (Finset.univ:Finset V)⊆insert x (A∪B) := fun v _=>hcover v
  have h₁:=Finset.card_le_card hsub
  have h₂:=Finset.card_insert_le x (A∪B)
  have h₃:=Finset.card_union_le A B
  simp only [Finset.card_univ] at h₁
  omega

theorem endpoint_conflict_no_index (F : SimpleGraph V) (A B : Finset V) (x : V)
    (hAB : Disjoint A B) (hxB : x∉B)
    (hF : F.support⊆(insert x A:Set V)) : ∀ u∈B,∀ w,¬F.Adj u w := by
  intro u hu w he
  have huF : u∈F.support := ⟨w,he⟩
  have huA : u∈insert x A:=by simpa using hF huF
  rcases Finset.mem_insert.mp huA with hux|huA
  · exact hxB (hux ▸ hu)
  · exact Finset.disjoint_left.mp hAB huA hu

end Oberwolfach
