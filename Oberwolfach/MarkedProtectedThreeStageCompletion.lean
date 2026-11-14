module

public import Oberwolfach.MarkedProtectedThreeStageCoverage
public import Oberwolfach.MarkedPackingDisjointFromDeletion
public import Oberwolfach.MarkedThreeStageRestoration
public import Oberwolfach.MarkedTerminalCompletionBetweenHosts

@[expose] public section

/-! Assemble the three constructed marked packings. Physical disjointness
and complete outside coverage are deduced from their actual deleted hosts;
the final divisibility and protected-star identities follow by subtraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 28000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_protected_three_stage_completion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hd:1≤d) (hm:1≤m)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hH:∀ x u,¬(H false x u∧H true x u))
    (I T:Finset V) (J W:Finset U) (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T)
    (KR:SimpleGraph V) (KS:SimpleGraph (V⊕U))
    (hKR:∀ x y,KR.Adj x y→x∈I∧y∈I)
    (hKS:∀ x u,KS.Adj (Sum.inl x) (Sum.inr u)→x∈I∧u∈J):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1;let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1;let khead:=fun e:K=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S m→
    ∀ ME MD MU:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ C∈ME,∀ C'∈ME,C≠C'→Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources C'))→
    (∀ C∈MD,∀ C'∈MD,C≠C'→Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources C'))→
    (∀ C∈MU,∀ C'∈MU,C≠C'→Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources C'))→
    let FE:=ME.biUnion markedWheelPhysicalResources
    let FD:=MD.biUnion markedWheelPhysicalResources
    let FU:=MU.biUnion markedWheelPhysicalResources
    let ER:=markedPackingRimGraph ME
    let DR:=markedPackingRimGraph MD
    let ES:=markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)
    let DS:=markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs);
    Disjoint DR (KR⊔ER)→
    (∀ x u,markedPackingSpokes MD x u→¬(KS⊔ES).Adj (Sum.inl x) (Sum.inr u))→
    Disjoint (markedPackingRimGraph MU) (ER⊔DR)→
    (∀ x u,markedPackingSpokes MU x u→¬(ES⊔DS).Adj (Sum.inl x) (Sum.inr u))→
    ∀ E₀:Finset (Finset V⊕(V×U)),
    FE.filter (markedInnerResource I J)=E₀→FD.filter (markedInnerResource I J)=∅→
    FU.filter (markedInnerResource I J)=FU.filter (markedInnerResource (I\T) (J\W))→
    (∀ e∈E₀,markedStarResource T W e)→E₀.filter (markedInnerResource T W)=∅→
    (∀ j x y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) j x y=1→
      ¬(KR⊔ER).Adj x (if j then π y else y)→
      markedStarResource T W (Sum.inl ({x,if j then π y else y}:Finset V))→
      Sum.inl ({x,if j then π y else y}:Finset V)∈FD)→
    (∀ j x u,H j x u→¬(KS⊔ES).Adj (Sum.inl x) (Sum.inr u)→
      markedStarResource T W (Sum.inr (x,u))→Sum.inr (x,u)∈FD)→
    (∀ j x y,x∉T→y∉T→markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) j x y=1→
      ¬(ER⊔DR).Adj x (if j then π y else y)→x∉I∨y∉I→
      Sum.inl ({x,if j then π y else y}:Finset V)∈FU)→
    (∀ j x u,x∉T→u∉W→H j x u→¬(ES⊔DS).Adj (Sum.inl x) (Sum.inr u)→x∉I∨u∉J→
      Sum.inr (x,u)∈FU)→
    ∃ N:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
      (∀ C∈N,∀ C'∈N,C≠C'→Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources C'))∧
      N.biUnion markedWheelPhysicalResources=FE∪FD∪FU∧
      let A':=Finset.univ\N.biUnion markedWheelArcs
      let S':=S\N.biUnion markedWheelSpokePairs
      let B:=markedFiniteResources tail head ktail khead π Finset.univ S
      let L:=markedFiniteResources tail head ktail khead π A' S'
      let removed:=B.filter (markedInnerResource I J)\L;
      MarkedRemainderDivisible tail head ktail khead (H true) A' S' m∧
      (∀ a∈A',Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)∧
      (∀ z∈S',z.1∈I∧z.2∈J)∧L=B\N.biUnion markedWheelPhysicalResources∧
      removed=E₀∪FU.filter (markedInnerResource (I\T) (J\W))∧
      removed.filter (markedStarResource T W)=E₀∧removed.filter (markedInnerResource T W)=∅∧
      ∀ p:Finset V⊕(V×U)→Prop,
        (removed.filter p).card≤(E₀.filter p).card+
          ((FU.filter (markedInnerResource (I\T) (J\W))).filter p).card:=by
  intro E K tail head ktail khead S hdiv ME MD MU hME hMD hMU FE FD FU ER DR ES DS
    hMDR hMDS hMUR hMUS E₀ hE hD hU hstar hdeep hdeepR hdeepS hactiveR hactiveS
  have hES:∀ x u,markedPackingSpokes ME x u→ES.Adj (Sum.inl x) (Sum.inr u):=by
    intro x u h
    apply (markedFiniteSpokeGraph_adj _ x u).mpr
    obtain ⟨C,hC,hu,hx⟩:=h
    exact Finset.mem_biUnion.mpr ⟨C,hC,(markedWheel_spoke_resource C (x,u)).mpr
      ((markedWheelPhysicalResources_spoke C x u).mpr ⟨hu,hx⟩)⟩
  have hDS:∀ x u,markedPackingSpokes MD x u→DS.Adj (Sum.inl x) (Sum.inr u):=by
    intro x u h
    apply (markedFiniteSpokeGraph_adj _ x u).mpr
    obtain ⟨C,hC,hu,hx⟩:=h
    exact Finset.mem_biUnion.mpr ⟨C,hC,(markedWheel_spoke_resource C (x,u)).mpr
      ((markedWheelPhysicalResources_spoke C x u).mpr ⟨hu,hx⟩)⟩
  have hED:Disjoint FE FD:=marked_packing_disjoint_from_deletion hm (by omega) ME MD (KR⊔ER) (KS⊔ES)
    le_sup_right (fun x u h=>Or.inr (hES x u h)) hMDR hMDS
  have hEU:Disjoint FE FU:=marked_packing_disjoint_from_deletion hm (by omega) ME MU (ER⊔DR) (ES⊔DS)
    le_sup_left (fun x u h=>Or.inl (hES x u h)) hMUR hMUS
  have hDU:Disjoint FD FU:=marked_packing_disjoint_from_deletion hm (by omega) MD MU (ER⊔DR) (ES⊔DS)
    le_sup_right (fun x u h=>Or.inr (hDS x u h)) hMUR hMUS
  have hsub:FE∪FD∪FU⊆markedFiniteResources tail head ktail khead π Finset.univ S:=by
    intro e he
    have hpack (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)))
        (h:e∈M.biUnion markedWheelPhysicalResources):e∈markedFiniteResources tail head ktail khead π Finset.univ S:=by
      obtain ⟨C,hC,heC⟩:=Finset.mem_biUnion.mp h
      exact marked_wheel_resources_in_full_host tail head ktail khead (H false) (H true) π m (3*d) C heC
    rcases Finset.mem_union.mp he with he|he
    · rcases Finset.mem_union.mp he with he|he
      · exact hpack ME he
      · exact hpack MD he
    · exact hpack MU he
  obtain ⟨hcovR,hcovS⟩:=marked_protected_three_stage_coverage P π d m σ H I T J W hI hT KR KS hKR hKS
    ME MD MU hdeepR hdeepS hactiveR hactiveS
  exact marked_three_stage_restoration hm (by omega) (markedSampleArc_physical_injective P π (3*d) _)
    hH Finset.univ S hdiv ME MD MU hME hMD hMU hED hEU hDU I T J W E₀ hE hD hU hstar hdeep hsub
    (fun a _=>hcovR a) (fun z hz=>hcovS z.1 z.2 (Finset.mem_filter.mp hz).2)

end Oberwolfach
