module

public import Oberwolfach.MarkedInnerFreePackingGraphs
public import Oberwolfach.MarkedProtectedPairFromChangeGraphs
public import Oberwolfach.RawMarkedRimDeletion
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion

@[expose] public section
/-! Deleting an inner-resource-free packing preserves the full protected
pair, not merely its active subpair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color E K:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_inner_free_packing_preserves_typed_pair
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (I:Finset V) (J:Finset U) (hI:∀ x,x∈I→π x∈I)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hinner:(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅):
    let FR:=markedPackingRimGraph M
    let FS:=markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)
    let σ':=rawMarkedDeleteRims σ FR.edgeFinset
    let H':=markedDeletePhysicalSpokes H FS
    (∀ mark x y,x∈I→y∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>σ' (Sum.inl e)) mark x y=1)) ∧
    (∀ j v u,v∈I→u∈J→(H j v u↔H' j v u)) :=by
  classical
  intro FR FS σ' H'
  obtain ⟨hFR,hFS⟩:=marked_inner_free_packing_graphs M I J hinner
  refine marked_protected_pair_from_change_graphs P π d σ σ' H H' I J FR FS hI ?_ ?_ hFR hFS
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
