module

public import Oberwolfach.MarkedFirstPackingGraphsAvoidActive
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion

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

theorem marked_first_packing_preserves_active_typed_pair
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
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U))
      (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)))
      (R:Finset (Finset V⊕(V×U))),
    (∀ e∈markedFiniteResources tail head ktail khead π A S,markedStarResource T W e)→
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      R.filter (markedStarResource T W)→
    let FR:=markedSampleArcSetGraph P π d σ (A∪M.biUnion markedWheelArcs)
    let FS:=markedFiniteSpokeGraph (S∪M.biUnion markedWheelSpokePairs)
    let σ':=rawMarkedDeleteRims σ FR.edgeFinset
    let H':=markedDeletePhysicalSpokes H FS
    (∀ mark x y,x∈I\T→y∈I\T→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>σ' (Sum.inl e)) mark x y=1)) ∧
    (∀ j v u,v∈I\T→u∈J\W→(H j v u↔H' j v u)) :=by
  intro E K tail head ktail khead A S M R hA hM FR FS σ' H'
  obtain ⟨hFR,hFS⟩:=marked_first_packing_graphs_avoid_active_pair P π d m σ H I T J W hI hT A S M R hA hM
  have hactive:∀ x,x∈I\T→π x∈I\T:=by
    intro x hx
    obtain ⟨hxi,hxt⟩:=Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨(hI x).mpr hxi,fun hh=>hxt ((hT x).mp hh)⟩
  refine marked_protected_pair_from_change_graphs P π d σ σ' H H' (I\T) (J\W) FR FS hactive ?_ ?_ hFR hFS
  · intro a hchange
    by_contra hnot
    apply hchange
    rw [rawMarkedDeleteRims_rims]
    simpa only [hnot,not_false_eq_true,and_true]
  · intro j v u hchange
    by_contra hnot
    apply hchange
    change H j v u ↔ H j v u ∧ ¬FS.Adj (Sum.inl v) (Sum.inr u)
    simp [hnot]
end Oberwolfach
