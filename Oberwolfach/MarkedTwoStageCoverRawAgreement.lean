module

public import Oberwolfach.MarkedFirstStarFilteredPacking
public import Oberwolfach.MarkedInnerFreePackingPreservesPair
public import Oberwolfach.MarkedRawPairUnchangedFromGraphs

@[expose] public section
/-! Sequential protection for the actual first star-filtered deletion and
an inner-resource-free deep packing. No property of the larger inner pair is
claimed for the first deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_two_stage_cover_preserves_active_raw_pair
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
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let tail':=fun e:E'=>e.val.1
    let head':=fun e:E'=>e.val.2
    let ktail':=fun e:K'=>e.val.1
    let khead':=fun e:K'=>e.val.2
    ∀ (MD:Finset (MarkedWheel tail' head' ktail' khead' m π (3*d) (H' false) (H' true))),
    (MD.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅→
    let σ'':=rawMarkedDeleteRims σ' (markedPackingRimGraph MD).edgeFinset
    let H'':=markedDeletePhysicalSpokes H' (markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs))
    ∀ {X Y:Type} [Fintype X] [Fintype Y] [LinearOrder X] [DecidableEq Y]
      (f:X→V) (g:Y→U),(∀ x,f x∈I\T)→(∀ u,g u∈J\W)→
    rawMarkedRestrictPair f g σ''=rawMarkedRestrictPair f g σ ∧
    (fun b x u=>H'' b (f x) (g u))=(fun b x u=>H b (f x) (g u)) :=by
  intro E K tail head ktail khead A₀ S₀ M R hM A S FR FS σ' H' E' K' tail' head' ktail' khead' MD hMD σ'' H'' X Y _ _ _ _ f g hf hg
  have hA:=marked_star_filtered_resources tail head ktail khead π A₀ S₀ T W hT
  obtain ⟨hFR,hFS⟩:=marked_first_packing_graphs_avoid_active_pair P π d m σ H I T J W hI hT A S M R hA hM
  obtain ⟨hDR,hDS⟩:=marked_inner_free_packing_graphs MD I J hMD
  have hfI:∀ x,f x∈I:=fun x=>(Finset.mem_sdiff.mp (hf x)).1
  have hgJ:∀ u,g u∈J:=fun u=>(Finset.mem_sdiff.mp (hg u)).1
  obtain ⟨h1r,h1s⟩:=marked_raw_pair_unchanged_from_graphs σ H FR FS (I\T) (J\W) hFR hFS f g hf hg
  obtain ⟨h2r,h2s⟩:=marked_raw_pair_unchanged_from_graphs σ' H' (markedPackingRimGraph MD)
    (markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) I J hDR hDS f g hfI hgJ
  exact ⟨h2r.trans h1r,h2s.trans h1s⟩

end Oberwolfach
