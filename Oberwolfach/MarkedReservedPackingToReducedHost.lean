module

public import Oberwolfach.MarkedReservedResourceGraphs
public import Oberwolfach.MarkedReservedResourceDeletionProtection

@[expose] public section
/-! A packing disjoint from the reserved resources has the same physical
wheels in the host obtained by deleting the two reserved graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_disjoint_packing_transfers_to_reserved_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))→
    Disjoint C (M.biUnion markedWheelPhysicalResources)→
    let DR:=physicalEdgeGraph (markedReservedRimPairs C)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let t':=fun e:E'=>e.val.1
    let h':=fun e:E'=>e.val.2
    let kt':=fun e:K'=>e.val.1
    let kh':=fun e:K'=>e.val.2;
    ∃ M':Finset (MarkedWheel t' h' kt' kh' m π (3*d) (H' false) (H' true)),
      (∀ W∈M',∀ Z∈M',W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      M'.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources:=by
  intro E K tail head ktail khead M hM hdis DR DS σ' H' E' K' t' h' kt' kh'
  let S:=M.biUnion markedWheelPhysicalResources
  have hgraphs:=marked_reserved_resource_graphs C
  have hR:∀ x y,Sum.inl ({x,y}:Finset V)∈S→¬DR.Adj x y:=by
    intro x y he hxy
    have hc:Sum.inl ({x,y}:Finset V)∈C:=(hgraphs.1 x y).mp hxy |>.2
    exact Finset.disjoint_left.mp hdis hc he
  have hS:∀ v u,Sum.inr (v,u)∈S→¬DS.Adj (Sum.inl v) (Sum.inr u):=by
    intro v u he huv
    exact Finset.disjoint_left.mp hdis ((hgraphs.2.1 v u).mp huv) he
  obtain ⟨hE,hK,hsp⟩:=marked_reserved_resources_survive_physical_deletion P π d σ H S DR DS hR hS
  have hEA:∀ e:E,Sum.inl ({tail e,head e}:Finset V)∈S→∃ e':E',t' e'=tail e∧h' e'=head e:=by
    intro e he
    obtain ⟨e',he'⟩:=hE e he
    exact ⟨e',congrArg Prod.fst he',congrArg Prod.snd he'⟩
  have hKA:∀ e:K,Sum.inl ({ktail e,π (khead e)}:Finset V)∈S→∃ e':K',kt' e'=ktail e∧kh' e'=khead e:=by
    intro e he
    obtain ⟨e',he'⟩:=hK e he
    exact ⟨e',congrArg Prod.fst he',congrArg Prod.snd he'⟩
  exact marked_decomposition_transfer_on_resources S hEA hKA
    (fun v u hc hh=>hsp false v u hc hh) (fun v u hc hh=>hsp true v u hc hh) ⟨M,hM,rfl⟩
end Oberwolfach
