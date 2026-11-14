module

public import Oberwolfach.MarkedSupportedResourceFamilies
public import Oberwolfach.MarkedInnerResources

@[expose] public section

/-! Relate the auxiliary endpoint exclusion in the absorber construction
with the physical induced-edge exclusion in iterative absorption. The
row set must be invariant under the successor permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

theorem marked_physical_edge_inner_iff
    (X:Finset V) (hX:∀ v,π v∈X↔v∈X) (a:E⊕K):
    markedPhysicalEdge tail head ktail khead π a⊆X↔
      Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X:=by
  cases a with
  | inl a=>simp only [markedPhysicalEdge,Finset.insert_subset_iff,
      Finset.singleton_subset_iff,Sum.elim_inl]
  | inr a=>simp only [markedPhysicalEdge,Finset.insert_subset_iff,
      Finset.singleton_subset_iff,Sum.elim_inr,hX]

theorem marked_old_resource_iff_inner
    (X:Finset V) (Z:Finset U) (hX:∀ v,π v∈X↔v∈X)
    (e:Finset V⊕(V×U))
    (hs:match e with | Sum.inl a=>∃ t:E⊕K,markedPhysicalEdge tail head ktail khead π t=a | Sum.inr _=>True):
    MarkedOldResource tail head ktail khead π X Z e↔markedInnerResource X Z e:=by
  cases e with
  | inl e=>
    constructor
    · rintro ⟨a,ha,ht,hh⟩
      rw [←ha]
      exact (marked_physical_edge_inner_iff X hX a).mpr ⟨ht,hh⟩
    · intro hi
      obtain ⟨a,ha⟩:=hs
      have hh:(markedPhysicalEdge tail head ktail khead π a)⊆X:=by rw [ha];exact hi
      exact ⟨a,ha,(marked_physical_edge_inner_iff X hX a).mp hh⟩
  | inr z=>rfl

theorem marked_reserved_absorber_avoids_inner
    (C:MarkedSupportedEdgeSet tail head ktail khead π U)
    (X:Finset V) (Z:Finset U) (hX:∀ v,π v∈X↔v∈X)
    (hC:∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π X Z e):
    C.edges.filter (markedInnerResource X Z)=∅:=by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hi⟩:=Finset.mem_filter.mp he
  apply hC e he
  apply (marked_old_resource_iff_inner X Z hX e ?_).mpr hi
  cases e with
  | inl e=>obtain ⟨a,ha,_,_⟩:=C.supported _ he;exact ⟨a,ha⟩
  | inr z=>trivial

end Oberwolfach
