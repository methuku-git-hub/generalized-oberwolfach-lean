module

public import Oberwolfach.MarkedHostRawEncoding
public import Oberwolfach.MarkedHostArcEquivalences

@[expose] public section

/-! Exact occurrence maps for the encoded modified host, while its
protected inner coordinates and all interval coordinates are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

def markedRawHostOrdinaryArcEquiv
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e)))
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (hI:∀ v,π v∈I↔v∈I)
    (hAgree:∀ mark x y,x∈I → y∈I →
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y))) :
    E ≃ MarkedSampleArc P π (3*d)
      (fun e=>rawMarkedEncodeHost tail head ktail khead π σ I (Sum.inl e)) false :=
  Equiv.ofBijective (fun e=>⟨(tail e,head e),
    (rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree false _ _).mpr ⟨e,rfl,rfl⟩⟩) (by
    constructor
    · intro a c hac
      have ht:tail a=tail c:=congrArg (fun e=>e.val.1) hac
      have hh:head a=head c:=congrArg (fun e=>e.val.2) hac
      have he:(Sum.inl a:E⊕K)=Sum.inl c:=hp (by simp only [markedPhysicalEdge,Sum.elim_inl,ht,hh])
      exact Sum.inl.inj he
    · intro e
      obtain ⟨a,ht,hh⟩:=(rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree false _ _).mp e.property
      exact ⟨a,Subtype.ext (Prod.ext ht hh)⟩)

def markedRawHostMarkedArcEquiv
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e)))
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (hI:∀ v,π v∈I↔v∈I)
    (hAgree:∀ mark x y,x∈I → y∈I →
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y))) :
    K ≃ MarkedSampleArc P π (3*d)
      (fun e=>rawMarkedEncodeHost tail head ktail khead π σ I (Sum.inl e)) true :=
  Equiv.ofBijective (fun e=>⟨(ktail e,khead e),
    (rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree true _ _).mpr ⟨e,rfl,rfl⟩⟩) (by
    constructor
    · intro a c hac
      have ht:ktail a=ktail c:=congrArg (fun e=>e.val.1) hac
      have hh:khead a=khead c:=congrArg (fun e=>e.val.2) hac
      have he:(Sum.inr a:E⊕K)=Sum.inr c:=hp (by simp only [markedPhysicalEdge,Sum.elim_inr,ht,hh])
      exact Sum.inr.inj he
    · intro e
      obtain ⟨a,ht,hh⟩:=(rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree true _ _).mp e.property
      exact ⟨a,Subtype.ext (Prod.ext ht hh)⟩)

theorem marked_raw_host_encoding_exact
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e)))
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (hI:∀ v,π v∈I↔v∈I)
    (hAgree:∀ mark x y,x∈I → y∈I →
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y))) :
    ∃ τ:RawMarkedOutcome V U Γ Color,
      (∀ e,τ (Sum.inr e)=σ (Sum.inr e)) ∧
      (∀ e:Sym2 V,e.toFinset⊆I → τ (Sum.inl e)=σ (Sum.inl e)) ∧
      ∃ e:E ≃ MarkedSampleArc P π (3*d) (fun a=>τ (Sum.inl a)) false,
      ∃ k:K ≃ MarkedSampleArc P π (3*d) (fun a=>τ (Sum.inl a)) true,
        (∀ a,(e a).val=(tail a,head a)) ∧ (∀ a,(k a).val=(ktail a,khead a)) := by
  refine ⟨rawMarkedEncodeHost tail head ktail khead π σ I,(fun _=>rfl),?_,
    markedRawHostOrdinaryArcEquiv P π d tail head ktail khead hp hE hK σ I hI hAgree,
    markedRawHostMarkedArcEquiv P π d tail head ktail khead hp hE hK σ I hI hAgree,
    (fun _=>rfl),(fun _=>rfl)⟩
  exact rawMarkedEncodeHost_inner_coordinates tail head ktail khead π σ I

end Oberwolfach
