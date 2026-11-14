module

public import Oberwolfach.MarkedInnerFreePackingPreservesPair
public import Oberwolfach.MarkedInnerStarAvoidsActive

@[expose] public section
/-! The first packing's stated inner-resource identity preserves the active
inner pair under its physical deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color E K:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_star_controlled_packing_preserves_active_pair
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (I T:Finset V) (J W:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (A:Finset (Finset V⊕(V×U)))
    (hfilter:(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      A.filter (markedStarResource T W)):
    let FR:=markedPackingRimGraph M
    let FS:=markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)
    let σ':=rawMarkedDeleteRims σ FR.edgeFinset
    let H':=markedDeletePhysicalSpokes H FS
    (∀ mark x y,x∈I\T→y∈I\T→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>σ' (Sum.inl e)) mark x y=1)) ∧
    (∀ j v u,v∈I\T→u∈J\W→(H j v u↔H' j v u)) :=by
  have hstar:∀ e∈M.biUnion markedWheelPhysicalResources,
      markedInnerResource I J e→markedStarResource T W e:=by
    intro e he hi
    have hh:e∈(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J):=
      Finset.mem_filter.mpr ⟨he,hi⟩
    rw [hfilter] at hh
    exact (Finset.mem_filter.mp hh).2
  have hinner:=marked_inner_star_avoids_active (M.biUnion markedWheelPhysicalResources) I T J W hstar
  have hactive:∀ x,x∈I\T→π x∈I\T:=by
    intro x hx
    obtain ⟨hxi,hxt⟩:=Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨(hI x).mpr hxi,fun hh=>hxt ((hT x).mp hh)⟩
  exact marked_inner_free_packing_preserves_typed_pair P π d σ H (I\T) (J\W) hactive M hinner
end Oberwolfach
