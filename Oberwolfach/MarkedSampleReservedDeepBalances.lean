module

public import Oberwolfach.MarkedFinitePhysicalDeletion
public import Oberwolfach.MarkedSampleDeletionLocalBalances
public import Oberwolfach.MarkedDeepBalanceAfterPacking

@[expose] public section

/-! Local deep balances in the actual raw sample after reserving the inner
star and removing the constructed wheel packing. No global divisibility
of the temporary star is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_reserved_star_packing_balances
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (hH:∀ x u,¬(H false x u∧H true x u)) (T:Finset V) (W:Finset U):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    ∀ (C:Finset (E₀⊕E₁)) (R:Finset (V×U)),R⊆S→
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S m→
    MarkedRemainderDivisible tail head ktail khead (H true) C R m→
    let KA:=C.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=R.filter (fun z=>z.1∈T∨z.2∈W)
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ X∈M,∀ Y∈M,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))→
    M.biUnion markedWheelArcs⊆Finset.univ\KA→
    M.biUnion markedWheelSpokePairs⊆S\KS→
    let DR:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)
    let DS:=markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let src':=Sum.elim (fun e:E₀'=>e.val.1) (fun e:E₁'=>e.val.1)
    let dst':=Sum.elim (fun e:E₀'=>e.val.2) (fun e:E₁'=>e.val.2)
    (∀ v∈T,
      (Finset.univ.filter (fun a=>dst' a=v)).card=(Finset.univ.filter (fun a=>src' a=v)).card ∧
      (Finset.univ.filter (fun a=>dst' a=v)).card=
        (Finset.univ.filter (fun z:V×U=>(H' false z.1 z.2∨H' true z.1 z.2)∧z.1=v)).card ∧
      (Finset.univ.filter (fun a=>dst' a=v∧markedArcType a=true)).card=
        (Finset.univ.filter (fun z:V×U=>H' true z.1 z.2∧z.1=v)).card) ∧
    (∀ u∈W,Fintype.card (hubNeighbourClass (H' false) (H' true) u false)=
      m*Fintype.card (hubNeighbourClass (H' false) (H' true) u true)):=by
  intro E₀ E₁ tail head ktail khead S C R hRS houter hinner KA KS M hM hMA hMS
  let DR:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)
  let DS:=markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)
  have hbal:=marked_reserved_star_and_packing_deep_balances Finset.univ C S R
    (Finset.subset_univ C) hRS houter hinner T W hH M hM hMA hMS
  have harcs:Finset.univ.filter (fun a:E₀⊕E₁=>
      Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉DR.edgeFinset)=
      (Finset.univ\KA)\M.biUnion markedWheelArcs:=by
    rw [markedSampleArcSetGraph_remaining]
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union]
    tauto
  have hspokes:Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧
      ¬DS.Adj (Sum.inl z.1) (Sum.inr z.2))=(S\KS)\M.biUnion markedWheelSpokePairs:=by
    ext z
    simp only [DS,markedFiniteSpokeGraph_adj,S,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_sdiff,Finset.mem_union]
    tauto
  constructor
  · intro v hv
    apply marked_sample_physical_deletion_local_row_balances P π d σ H DR DS v
    · rw [harcs];exact (hbal.1 v hv).1
    · rw [harcs,hspokes];exact (hbal.1 v hv).2.1
    · rw [harcs,hspokes];exact (hbal.1 v hv).2.2
  · intro u hu
    apply marked_sample_physical_deletion_local_hub_balance H DS u m (fun x=>hH x u)
    rw [hspokes]
    exact hbal.2 u hu

end Oberwolfach
