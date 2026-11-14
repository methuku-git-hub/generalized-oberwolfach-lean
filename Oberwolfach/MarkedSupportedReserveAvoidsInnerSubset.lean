module

public import Oberwolfach.MarkedOldInnerAgreement

@[expose] public section
/-! A supported reserve which avoids an old pair also avoids every
permutation-invariant inner pair contained in it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}
theorem marked_supported_reserve_avoids_inner_subset
    (C:MarkedSupportedEdgeSet tail head ktail khead π U) (I W:Finset V) (J B:Finset U)
    (hI:∀ v,π v∈I↔v∈I) (hIW:I⊆W) (hJB:J⊆B)
    (hC:∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π W B e):
    ∀ e∈C.edges,¬markedInnerResource I J e:=by
  intro e he hi
  apply hC e he
  cases e with
  | inl e=>
    obtain ⟨a,ha,_,_⟩:=C.supported _ he
    have heI:markedPhysicalEdge tail head ktail khead π a⊆I:=by rw [ha];exact hi
    obtain ⟨ht,hh⟩:=(marked_physical_edge_inner_iff I hI a).mp heI
    exact ⟨a,ha,hIW ht,hIW hh⟩
  | inr z=>exact ⟨hIW hi.1,hJB hi.2⟩
end Oberwolfach
