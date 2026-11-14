module

public import Oberwolfach.MarkedTwoStageCoverRawAgreement
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

theorem marked_two_stage_cover_preserves_reference_inner_raw_pair
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
    ∀ {X Y Z:Type} [Fintype X] [Fintype Y] [Fintype Z] [LinearOrder X] [DecidableEq Z]
      (f:X→Y) (fA:Y→V) (gA:Z→U) (Zinner:Finset Z),
    ((Finset.univ.image f).image fA=I\T)→(Zinner.image gA=J\W)→
    rawMarkedRestrictPair (fun x=>fA (f x)) (fun z:Zinner=>gA z) σ''=
      rawMarkedRestrictPair (fun x=>fA (f x)) (fun z:Zinner=>gA z) σ ∧
    (fun b x (u:Zinner)=>H'' b (fA (f x)) (gA u))=
      (fun b x (u:Zinner)=>H b (fA (f x)) (gA u)) :=by
  intro E K tail head ktail khead A₀ S₀ M R hM A S FR FS σ' H' E' K' tail' head' ktail' khead' MD hMD σ'' H'' X Y Z _ _ _ _ _ f fA gA Zinner hX hZ
  have hf:∀ x,fA (f x)∈I\T:=by
    intro x
    rw [←hX]
    exact Finset.mem_image.mpr ⟨f x,Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩,rfl⟩
  have hg:∀ u:Zinner,gA u∈J\W:=by
    intro u
    rw [←hZ]
    exact Finset.mem_image.mpr ⟨u.val,u.property,rfl⟩
  exact marked_two_stage_cover_preserves_active_raw_pair P π d m σ H I T J W hI hT A₀ S₀ M R hM MD hMD
    (fun x=>fA (f x)) (fun z:Zinner=>gA z) hf hg

end Oberwolfach
