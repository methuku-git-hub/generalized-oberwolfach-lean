module

public import Oberwolfach.MarkedReservedGraphsPackingIdentity

@[expose] public section
/-! Removing the physical resources of a wheel-decomposable reserved set
preserves divisibility in the actual reserved-deleted sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_reduced_host_divisible
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let R:=fun W:MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W;
    (∀ v u,¬(H false v u∧H true v u))→
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S m→
    ∀ C:Finset (Finset V⊕(V×U)),HasResourceDecomposition R C→
    let DR:=physicalEdgeGraph (markedReservedRimPairs C)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) m :=by
  intro E K tail head ktail khead S R hH hDiv C hDec DR DS σ' H' E' K'
  obtain ⟨M,hM,hMC⟩:=hDec
  let FA:=M.biUnion markedWheelArcs
  let FS:=M.biUnion markedWheelSpokePairs
  let Full:=markedFiniteResources tail head ktail khead π Finset.univ S
  have hCsub:C⊆Full:=by
    rw [←hMC]
    intro z hz
    obtain ⟨W,hW,hz⟩:=Finset.mem_biUnion.mp hz
    exact marked_wheel_resources_in_full_host _ _ _ _ (H false) (H true) π m (3*d) W hz
  have hp:=markedSampleArc_physical_injective P π (3*d) (fun a=>σ (Sum.inl a))
  have hMS:FA⊆Finset.univ ∧ FS⊆S:=by
    apply marked_packing_resources_contained hp M Finset.univ S
    change M.biUnion markedWheelPhysicalResources⊆Full
    rw [hMC]
    exact hCsub
  have hDivRem:MarkedRemainderDivisible tail head ktail khead (H true) (Finset.univ\FA) (S\FS) m:=
    marked_packing_remainder_divisible hH Finset.univ S hDiv M hM hMS.1 hMS.2
  have hCanonical : let σNext:=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ FA).edgeFinset
      let HNext:=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph FS)
      let ENext:=MarkedSampleArc P π (3*d) (fun a=>σNext (Sum.inl a)) false
      let KNext:=MarkedSampleArc P π (3*d) (fun a=>σNext (Sum.inl a)) true;
      MarkedRemainderDivisible (fun e:ENext=>e.val.1) (fun e=>e.val.2)
        (fun e:KNext=>e.val.1) (fun e=>e.val.2) (HNext true) Finset.univ
        (Finset.univ.filter (fun z:V×U=>HNext false z.1 z.2∨HNext true z.1 z.2)) m:=by
    apply (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mp
    intro z i
    rw [(marked_canonical_deleted_balance_values P π d m σ H FA FS Finset.univ Finset.univ z i).1]
    exact (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mpr hDivRem z i
  have hgraphs:=marked_reserved_graphs_of_packing C M hMC
  have hR:markedSampleArcSetGraph P π d σ FA=DR:=by
    rw [show FA=M.biUnion markedWheelArcs from rfl,markedSampleArcSetGraph_packing]
    exact hgraphs.1
  have hS:markedFiniteSpokeGraph FS=DS:=hgraphs.2
  dsimp only [FA,FS] at hCanonical hR hS
  rw [hR,hS] at hCanonical
  exact hCanonical
end Oberwolfach
