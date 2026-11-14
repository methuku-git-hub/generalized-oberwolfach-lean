module

public import Oberwolfach.MarkedTwoStageTerminalAbsorber
public import Oberwolfach.MarkedSamplePhysicalDeletionLift

@[expose] public section
/-! A preselected absorber's terminal decomposition survives lifting from
the physically deleted host to the original marked host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_terminal_absorber_decomposition_lift
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (Reserve:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U)
    (habs:MarkedUniversalTerminalDeletionAbsorber P π d m σ H Reserve X Z)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hR:∀ x y,Sum.inl ({x,y}:Finset V)∈Reserve→¬DR.Adj x y)
    (hSavoid:∀ v u,Sum.inr (v,u)∈Reserve→¬DS.Adj (Sum.inl v) (Sum.inr u))
    (hXZ:∀ v∈X,∀ u∈Z,¬DS.Adj (Sum.inl v) (Sum.inr u)):
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let t':=fun e:E'=>e.val.1
    let h':=fun e:E'=>e.val.2
    let kt':=fun e:K'=>e.val.1
    let kh':=fun e:K'=>e.val.2;
    ∀ (A:Finset (E'⊕K')) (S:Finset (V×U)),
    (∀ a∈A,Sum.elim t' kt' a∈X∧Sum.elim h' kh' a∈X)→
    (∀ z∈S,z.1∈X∧z.2∈Z∧(H' false z.1 z.2∨H' true z.1 z.2))→
    MarkedRemainderDivisible t' h' kt' kh' (H' true) A S m→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W)
      (Reserve∪markedFiniteResources t' h' kt' kh' π A S):=by
  intro σ' H' E' K' t' h' kt' kh' A S hA hS hdiv E K
  have hh:=habs DR DS hR hSavoid hXZ A S hA hS hdiv
  obtain ⟨M,hM,hMres⟩:=hh.2.2
  let M':=M.image (markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H)
  have hlift:=markedPhysicalDeletedSamplePacking_lift P π d m σ DR DS H M hM
  exact ⟨M',hlift.2.1,hlift.1.trans hMres⟩
end Oberwolfach
