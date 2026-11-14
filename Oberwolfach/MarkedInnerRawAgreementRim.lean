module

public import Oberwolfach.MarkedInnerSelectedSampleAgreement

@[expose] public section
/-! Equality of raw physical coordinates on an invariant inner set preserves
both types of directed rims there. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_inner_raw_agreement_rims
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (hπ:∀v,π v∈I↔v∈I) (σ τ:RawMarkedOutcome V U Γ Color)
    (hAgree:∀e:Sym2 V,e.toFinset⊆I→τ (Sum.inl e)=σ (Sum.inl e)):
    ∀mark x y,x∈I→y∈I→
      (markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1) :=by
  intro mark x y hx hy
  cases mark with
  | false =>
    have heq:τ (Sum.inl s(x,y))=σ (Sum.inl s(x,y)):=by
      apply hAgree
      simpa only [Sym2.toFinset_mk_eq,Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hy
    rw [markedPhysicalRim_eq_one_iff,markedPhysicalRim_eq_one_iff]
    simp [heq]
  | true =>
    have hpy:π y∈I:=(hπ y).2 hy
    have heq:τ (Sum.inl s(x,π y))=σ (Sum.inl s(x,π y)):=by
      apply hAgree
      simpa only [Sym2.toFinset_mk_eq,Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hpy
    rw [markedPhysicalRim_eq_one_iff,markedPhysicalRim_eq_one_iff]
    simp [heq]
end Oberwolfach
