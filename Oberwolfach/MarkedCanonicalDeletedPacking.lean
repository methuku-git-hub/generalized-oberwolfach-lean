module

public import Oberwolfach.MarkedSamplePackingAvoidedSets
public import Oberwolfach.MarkedPhysicalDeletionComposition

@[expose] public section

/-! A packing in the current deleted sample has an exact original-host
realisation. Its occurrence sets avoid the prior deletion, and deleting it
from the current sample equals deleting the union in the original sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem markedPackingResourceEquality_spokePairs
    {E K E' K':Type} {tail head:E→V} {ktail khead:K→V}
    {tail' head':E'→V} {ktail' khead':K'→V} {m b m' b':ℕ} {π π':Equiv.Perm V}
    {H₀ HK H₀' HK':V→U→Prop}
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (N:Finset (MarkedWheel tail' head' ktail' khead' m' π' b' H₀' HK'))
    (he:M.biUnion markedWheelPhysicalResources=N.biUnion markedWheelPhysicalResources):
    M.biUnion markedWheelSpokePairs=N.biUnion markedWheelSpokePairs:=by
  ext s
  simp only [Finset.mem_biUnion,markedWheel_spoke_resource]
  have hs:Sum.inr s∈M.biUnion markedWheelPhysicalResources↔Sum.inr s∈N.biUnion markedWheelPhysicalResources:=by rw [he]
  simpa only [Finset.mem_biUnion] using hs

theorem marked_canonical_deleted_packing
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (A:Finset (E₀⊕E₁)) (B:Finset (V×U)),
    let DR:=markedSampleArcSetGraph P π d σ A
    let DS:=markedFiniteSpokeGraph B;
    ∀ M:Finset (MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H),
    (∀ Y∈M,∀ Z∈M,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))→
    let N:=M.image (markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H);
    N.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources∧
    (∀ Y∈N,∀ Z∈N,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))∧
    N.biUnion markedWheelArcs⊆Finset.univ\A∧N.biUnion markedWheelSpokePairs⊆S\B∧
    rawMarkedDeleteRims (rawMarkedDeleteRims σ DR.edgeFinset) (markedPackingRimGraph M).edgeFinset=
      rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ (A∪N.biUnion markedWheelArcs)).edgeFinset∧
    markedDeletePhysicalSpokes (markedDeletePhysicalSpokes H DS) (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs))=
      markedDeletePhysicalSpokes H (markedFiniteSpokeGraph (B∪N.biUnion markedWheelSpokePairs)):=by
  intro E₀ E₁ S A B DR DS M hM N
  obtain ⟨hres,hN,hR,hS⟩:=markedPhysicalDeletedSamplePacking_lift P π d m σ DR DS H M hM
  obtain ⟨ha,hb⟩:=marked_sample_packing_avoids_reserved_sets P π d m σ H A B N hR hS
  have hgraphs:markedPackingRimGraph N=markedPackingRimGraph M:=
    (markedPackingResourceEquality_graphs N M hres).1
  have hspokes:=markedPackingResourceEquality_spokePairs N M hres
  refine ⟨hres,hN,ha,hb,?_,?_⟩
  · rw [rawMarkedDeleteRims_sup,markedSampleArcSetGraph_union,markedSampleArcSetGraph_packing,hgraphs]
    congr!
  · rw [markedDeletePhysicalSpokes_sup,markedFiniteSpokeGraph_union,hspokes]

end Oberwolfach
