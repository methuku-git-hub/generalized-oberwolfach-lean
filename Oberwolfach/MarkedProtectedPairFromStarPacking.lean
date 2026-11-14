module

public import Oberwolfach.MarkedProtectedPairFromPacking
public import Oberwolfach.MarkedProtectedPairFromChangeGraphs

@[expose] public section
/-! A star-avoiding packing and prescribed changes that avoid the protected
pair give agreement of both typed hosts on that pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color E K:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_protected_pair_from_star_avoiding_packing
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (I:Finset V) (J:Finset U) (hI:∀ x,x∈I→π x∈I)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hstar:(M.biUnion markedWheelPhysicalResources).filter (markedStarResource I J)=∅)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U))
    (hER:∀ x∈I,∀ y∈I,¬ER.Adj x y)
    (hES:∀ x∈I,∀ u∈J,¬ES.Adj (Sum.inl x) (Sum.inr u)):
    let FR:=ER⊔markedPackingRimGraph M
    let FS:=ES⊔markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)
    (∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈FR.edgeFinset)→
    (∀ j v u,¬(H j v u↔H' j v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀ mark x y,x∈I→y∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1)) ∧
    (∀ j v u,v∈I→u∈J→(H j v u↔H' j v u)) :=by
  classical
  intro FR FS hRim hSpoke
  obtain ⟨hFR,hFS⟩:=marked_protected_pair_avoided_by_packing M I J hstar ER ES hER hES
  refine marked_protected_pair_from_change_graphs P π d σ τ H H' I J FR FS hI ?_ hSpoke hFR hFS
  intro a ha
  simpa only [SimpleGraph.mem_edgeFinset] using hRim a ha
end Oberwolfach
