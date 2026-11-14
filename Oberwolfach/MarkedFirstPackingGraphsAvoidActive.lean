module

public import Oberwolfach.MarkedStarControlledPackingGraphs
public import Oberwolfach.MarkedStarResourcesAvoidActiveGraphs
public import Oberwolfach.MarkedProtectedPairFromChangeGraphs
public import Oberwolfach.MarkedFiniteDeletionDegrees
public import Oberwolfach.RawMarkedRimDeletion

@[expose] public section
/-! The first cover's actual star resources and packing preserve the active
inner pair when their displayed resource identities hold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_first_packing_graphs_avoid_active_pair
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
    (∀ x∈I\T,∀ y∈I\T,¬FR.Adj x y) ∧
    (∀ x∈I\T,∀ u∈J\W,¬FS.Adj (Sum.inl x) (Sum.inr u)) :=by
  intro E K tail head ktail khead A S M R hA hM FR FS
  obtain ⟨hMR,hMS⟩:=marked_star_controlled_packing_graphs M I T J W R hM
  obtain ⟨hAR,hAS⟩:=marked_star_resources_avoid_active_graphs tail head ktail khead π A S I T J W hA
  have hFR:∀ x∈I\T,∀ y∈I\T,¬FR.Adj x y:=by
    intro x hx y hy h
    change (markedSampleArcSetGraph P π d σ (A∪M.biUnion markedWheelArcs)).Adj x y at h
    rw [markedSampleArcSetGraph_union P π d σ A (M.biUnion markedWheelArcs),
      markedSampleArcSetGraph_packing P π d m σ H M] at h
    rcases h with h|h
    · exact hAR x hx y hy h
    · exact hMR x hx y hy h
  have hFS:∀ x∈I\T,∀ u∈J\W,¬FS.Adj (Sum.inl x) (Sum.inr u):=by
    intro x hx u hu h
    change (markedFiniteSpokeGraph (S∪M.biUnion markedWheelSpokePairs)).Adj _ _ at h
    rw [markedFiniteSpokeGraph_union] at h
    rcases h with h|h
    · exact hAS x hx u hu h
    · exact hMS x hx u hu h
  exact ⟨hFR,hFS⟩
end Oberwolfach
