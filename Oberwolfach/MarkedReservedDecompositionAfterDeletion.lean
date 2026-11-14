module

public import Oberwolfach.MarkedReservedResourceDeletionProtection
public import Oberwolfach.MarkedDecompositionHostTransfer

@[expose] public section
/-! A fixed wheel-decomposable resource set remains wheel-decomposable
after physical deletions which avoid all its rim and spoke resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_reserved_decomposition_after_avoiding_deletions
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (C:Finset (Finset V⊕(V×U))) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hR:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬DR.Adj x y)
    (hS:∀ v u,Sum.inr (v,u)∈C→¬DS.Adj (Sum.inl v) (Sum.inr u)):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let t':=fun e:E'=>e.val.1
    let h':=fun e:E'=>e.val.2
    let kt':=fun e:K'=>e.val.1
    let kh':=fun e:K'=>e.val.2;
    HasResourceDecomposition
      (fun W:MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W) C→
    HasResourceDecomposition
      (fun W:MarkedWheel t' h' kt' kh' m π (3*d) (H' false) (H' true)=>markedWheelPhysicalResources W) C:=by
  intro E K tail head ktail khead σ' H' E' K' t' h' kt' kh' hdec
  obtain ⟨hE,hK,hsp⟩:=marked_reserved_resources_survive_physical_deletion P π d σ H C DR DS hR hS
  have hEA:∀ e:E,Sum.inl ({tail e,head e}:Finset V)∈C→∃ e':E',t' e'=tail e∧h' e'=head e:=by
    intro e he
    obtain ⟨e',he'⟩:=hE e he
    exact ⟨e',congrArg Prod.fst he',congrArg Prod.snd he'⟩
  have hKA:∀ e:K,Sum.inl ({ktail e,π (khead e)}:Finset V)∈C→∃ e':K',kt' e'=ktail e∧kh' e'=khead e:=by
    intro e he
    obtain ⟨e',he'⟩:=hK e he
    exact ⟨e',congrArg Prod.fst he',congrArg Prod.snd he'⟩
  exact marked_decomposition_transfer_on_resources C hEA hKA
    (fun v u hc hh=>hsp false v u hc hh) (fun v u hc hh=>hsp true v u hc hh) hdec
end Oberwolfach
