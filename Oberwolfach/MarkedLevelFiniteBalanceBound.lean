module

public import Oberwolfach.MarkedAdaptiveAgreementProperty

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def MarkedLevelFiniteBalanceBound (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (I:Finset V) (J:Finset U) (err:ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):Prop:=
  let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
  let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
  let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
  ∀ v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m I J v j|≤err
end Oberwolfach
