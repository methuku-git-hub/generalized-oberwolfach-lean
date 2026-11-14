module

public import Oberwolfach.MarkedReferenceCorrectionDeletion
public import Oberwolfach.MarkedCorrectionLocalIncidence

@[expose] public section
/-! The local bounds and corrected divisibility of a sparse correction supply
a valid reference deletion state, including both incidence representations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sparse_correction_reference_state
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
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      (H true) (Finset.univ\FA) (S\FS) m →
    ∃ D:MarkedReferenceDeletion P π d σ, D.arcs=FA ∧ D.spokes=FS ∧ D.Valid H m X Y γ σloss := by
  intro E K S FA FS hFS hprotect hArc hRow hCol hdiv
  have hp:=markedSampleArc_physical_injective P π (3*d) (fun a=>σ (Sum.inl a))
  have hi:=marked_correction_local_incidence_bound (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) FA FS B hB hp hArc hRow hCol
  exact marked_reference_correction_deletion P π d m σ H X Y γ σloss FA FS hFS hprotect
    (fun physical z=>(hi physical z).trans hbudget) hdiv
end Oberwolfach
