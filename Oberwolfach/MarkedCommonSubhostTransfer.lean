module

public import Oberwolfach.MarkedCommonSubhostAgreement
public import Oberwolfach.MarkedDecompositionHostTransfer

@[expose] public section
/-! Every typed arc, spoke and wheel of the common subhost transfers to
each of the two hosts without changing any physical resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_common_subhost_transfer_to_later
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ mark x y,markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=1→
      markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1)
    (hsp:∀ b v u,markedDeletePhysicalSpokes H DS b v u→H' b v u):
    let E:=MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) true
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let tail':=fun e:E'=>e.val.1
    let head':=fun e:E'=>e.val.2
    let ktail':=fun e:K'=>e.val.1
    let khead':=fun e:K'=>e.val.2;
    ∀ C L:Finset (Finset V⊕(V×U)),
      IsResourceAbsorber
        (fun W:MarkedWheel tail head ktail khead m π (3*d)
          (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true)=>markedWheelPhysicalResources W) L C →
      IsResourceAbsorber
        (fun W:MarkedWheel tail' head' ktail' khead' m π (3*d) (H' false) (H' true)=>markedWheelPhysicalResources W) L C :=by
  intro E K E' K' tail head ktail khead tail' head' ktail' khead' C L habs
  apply marked_absorber_transfer_on_resources
    (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
    (tail':=tail') (head':=head') (ktail':=ktail') (khead':=khead')
    (H₀:=markedDeletePhysicalSpokes H DS false) (HK:=markedDeletePhysicalSpokes H DS true)
    (H₀':=H' false) (HK':=H' true) (π:=π) (m:=m) (b:=3*d) C L
  · intro e _
    exact ⟨⟨e.val,hrim false e.val.1 e.val.2 e.property⟩,rfl,rfl⟩
  · intro e _
    exact ⟨⟨e.val,hrim true e.val.1 e.val.2 e.property⟩,rfl,rfl⟩
  · intro v u _ hv
    exact hsp false v u hv
  · intro v u _ hv
    exact hsp true v u hv
  · exact habs
end Oberwolfach
