module

public import Oberwolfach.MarkedCanonicalRemainderState

@[expose] public section
/-! The exact finite remainder produced by the sparse correction is divisible
in the canonical physically deleted sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_sparse_correction_canonical_divisible
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (DA:Finset (E⊕K)) (DS:Finset (V×U)),
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) (Finset.univ\DA) (S\DS) m→
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2)) m:=by
  intro E K S DA DS hdiv σ' H' E' K'
  have hp:=markedSampleArc_physical_injective P π (3*d) (fun e=>σ (Sum.inl e))
  have hres:=markedFiniteResources_sdiff (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) π hp Finset.univ DA S DS
  exact (marked_canonical_remainder_divisibility P π d m σ H DA (Finset.univ\DA) DS (S\DS) hdiv hres).2.2
end Oberwolfach
