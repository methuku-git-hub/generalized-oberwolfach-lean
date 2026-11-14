module

public import Oberwolfach.MarkedHostRimEncoding
public import Oberwolfach.MarkedWheelVertexEmbedding

@[expose] public section

/-! The categorical encoding preserves the actual ordinary and marked arc
identifiers bijectively, including both directed endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K : Type} [LinearOrder V]

def markedHostOrdinaryArcEquiv
    (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π b (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π b (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e))) :
    E ≃ MarkedSampleArc P π b (markedHostRimEncoding tail head ktail khead π) false :=
  Equiv.ofBijective (fun e=>⟨(tail e,head e),
    (markedHostRimEncoding_arcs P π b tail head ktail khead hp hE hK false _ _).mpr ⟨e,rfl,rfl⟩⟩) (by
    constructor
    · intro a c hac
      have ht:tail a=tail c:=congrArg (fun e=>e.val.1) hac
      have hh:head a=head c:=congrArg (fun e=>e.val.2) hac
      have he:(Sum.inl a:E⊕K)=Sum.inl c:=hp (by simp only [markedPhysicalEdge,Sum.elim_inl,Sum.elim_inr,ht,hh])
      exact Sum.inl.inj he
    · intro e
      obtain ⟨a,ht,hh⟩:=(markedHostRimEncoding_arcs P π b tail head ktail khead hp hE hK false _ _).mp e.property
      exact ⟨a,Subtype.ext (Prod.ext ht hh)⟩)

def markedHostMarkedArcEquiv
    (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π b (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π b (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e))) :
    K ≃ MarkedSampleArc P π b (markedHostRimEncoding tail head ktail khead π) true :=
  Equiv.ofBijective (fun e=>⟨(ktail e,khead e),
    (markedHostRimEncoding_arcs P π b tail head ktail khead hp hE hK true _ _).mpr ⟨e,rfl,rfl⟩⟩) (by
    constructor
    · intro a c hac
      have ht:ktail a=ktail c:=congrArg (fun e=>e.val.1) hac
      have hh:khead a=khead c:=congrArg (fun e=>e.val.2) hac
      have he:(Sum.inr a:E⊕K)=Sum.inr c:=hp (by simp only [markedPhysicalEdge,Sum.elim_inl,Sum.elim_inr,ht,hh])
      exact Sum.inr.inj he
    · intro e
      obtain ⟨a,ht,hh⟩:=(markedHostRimEncoding_arcs P π b tail head ktail khead hp hE hK true _ _).mp e.property
      exact ⟨a,Subtype.ext (Prod.ext ht hh)⟩)

theorem markedHostOrdinaryArcEquiv_endpoints
    (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π b (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π b (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e))) (e:E) :
    (markedHostOrdinaryArcEquiv P π b tail head ktail khead hp hE hK e).val=(tail e,head e) := rfl

theorem markedHostMarkedArcEquiv_endpoints
    (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π b (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π b (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e))) (e:K) :
    (markedHostMarkedArcEquiv P π b tail head ktail khead hp hE hK e).val=(ktail e,khead e) := rfl

end Oberwolfach
