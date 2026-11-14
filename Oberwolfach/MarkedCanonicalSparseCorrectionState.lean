module

public import Oberwolfach.MarkedSparseCorrectionReferenceState
public import Oberwolfach.MarkedCanonicalCorrectionDivisibility

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_canonical_sparse_correction_reference_state
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Y:Finset U) (γ σloss B:ℝ) (hB:0≤B)
    (hbudget:6*B≤min γ σloss):
    let E:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false
    let K:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∀ (FA:Finset (E⊕K)) (FS:Finset (V×U)),
    FS⊆S →
    (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2) π FA FS).filter (markedInnerResource X Y)=∅ →
    (∀v,((FA.filter (fun a=>v=Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∨
      v=Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a)).card:ℝ)≤B) →
    (∀v,((FS.filter (fun z=>v=z.1)).card:ℝ)≤B) →
    (∀u,((FS.filter (fun z=>z.2=u)).card:ℝ)≤B) →
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ FA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph FS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
      (H' true) Finset.univ (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) m →
    ∃ D:MarkedReferenceDeletion P π d σ, D.arcs=FA ∧ D.spokes=FS ∧ D.Valid H m X Y γ σloss := by
  intro E K S FA FS hFS hprotect hArc hRow hCol σ' H' E' K' hdiv
  have hOld:=marked_canonical_correction_original_divisible P π d m σ H FA FS hdiv
  exact marked_sparse_correction_reference_state P π d m σ H X Y γ σloss B hB hbudget FA FS
    hFS hprotect hArc hRow hCol hOld
end Oberwolfach
