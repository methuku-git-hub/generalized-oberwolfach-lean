module

public import Oberwolfach.MarkedFirstPackingPreservesActiveTyped
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion
public import Oberwolfach.MarkedStarFilteredResources

@[expose] public section
/-! The first packing and star-filtered deletions preserve the typed
resources on the active inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_first_packing_star_filtered_preserves_active_typed_pair
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (I T:Finset V) (J W:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    ∀ (A₀:Finset (E⊕K)) (S₀:Finset (V×U))
      (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)))
      (R:Finset (Finset V⊕(V×U))),
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      R.filter (markedStarResource T W)→
    let A:=A₀.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let S:=S₀.filter (fun z=>z.1∈T∨z.2∈W)
    let FR:=markedSampleArcSetGraph P π d σ (A∪M.biUnion markedWheelArcs)
    let FS:=markedFiniteSpokeGraph (S∪M.biUnion markedWheelSpokePairs)
    let σ':=rawMarkedDeleteRims σ FR.edgeFinset
    let H':=markedDeletePhysicalSpokes H FS
    (∀ mark x y,x∈I\T→y∈I\T→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>σ' (Sum.inl e)) mark x y=1)) ∧
    (∀ j v u,v∈I\T→u∈J\W→(H j v u↔H' j v u)) :=by
  intro E K tail head ktail khead A₀ S₀ M R hM A S FR FS σ' H'
  have hA:=marked_star_filtered_resources tail head ktail khead π A₀ S₀ T W hT
  exact marked_first_packing_preserves_active_typed_pair P π d m σ H I T J W hI hT A S M R hA hM
end Oberwolfach
