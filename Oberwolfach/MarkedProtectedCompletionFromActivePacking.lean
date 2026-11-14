module

public import Oberwolfach.MarkedProtectedThreeStageCompletion
public import Oberwolfach.MarkedActiveCoverPackingLift

@[expose] public section

/-! Assemble the three constructed marked packings. Physical disjointness
and complete outside coverage are deduced from their actual deleted hosts;
the final divisibility and protected-star identities follow by subtraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A B Γ Color:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype B] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq B]

theorem marked_protected_completion_from_active_packing
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hd:1≤d) (hm:1≤m)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hH:∀ x u,¬(H false x u∧H true x u))
    (I T:Finset V) (J W:Finset U) (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T)
    (f:A↪oV) (g:B↪U) (ρ:Equiv.Perm A) (hf:∀ x,f (ρ x)=π (f x))
    (hfX:Finset.univ.image f=Finset.univ\T) (hgX:Finset.univ.image g=Finset.univ\W)
    (X:Finset A) (Z:Finset B) (hX:∀ x,f x∈I↔x∈X) (hZ:∀ u,g u∈J↔u∈Z)
    (KR:SimpleGraph V) (KS:SimpleGraph (V⊕U))
    (hKR:∀ x y,KR.Adj x y→x∈I∧y∈I)
    (hKS:∀ x u,KS.Adj (Sum.inl x) (Sum.inr u)→x∈I∧u∈J):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1;let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1;let khead:=fun e:K=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S m→
    ∀ ME MD:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ C∈ME,∀ C'∈ME,C≠C'→Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources C'))→
    (∀ C∈MD,∀ C'∈MD,C≠C'→Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources C'))→
    let FE:=ME.biUnion markedWheelPhysicalResources
    let FD:=MD.biUnion markedWheelPhysicalResources
    let ER:=markedPackingRimGraph ME
    let DR:=markedPackingRimGraph MD
    let ES:=markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)
    let DS:=markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs);
    Disjoint DR (KR⊔ER)→
    (∀ x u,markedPackingSpokes MD x u→¬(KS⊔ES).Adj (Sum.inl x) (Sum.inr u))→
    ∀ (DRtot:SimpleGraph V) (DStot:SimpleGraph (V⊕U)),DRtot=ER⊔DR→DStot=ES⊔DS→
    ∀ MA:Finset (MarkedActiveDeletedWheel f g P π ρ d m σ H DRtot DStot),
    (∀ C∈MA,∀ C'∈MA,C≠C'→Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources C'))→
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DRtot.edgeFinset)
    let HA:=fun j x u=>markedDeletePhysicalSpokes H DStot j (f x) (g u)
    let EA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let KA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true;
    (∀ a∈(Finset.univ:Finset (EA⊕KA))\MA.biUnion markedWheelArcs,
      Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a∈X∧Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a∈X)→
    (∀ s∈(Finset.univ.filter (fun s:A×B=>HA false s.1 s.2∨HA true s.1 s.2))\MA.biUnion markedWheelSpokePairs,
      s.1∈X∧s.2∈Z)→
    ∀ E₀:Finset (Finset V⊕(V×U)),
    FE.filter (markedInnerResource I J)=E₀→FD.filter (markedInnerResource I J)=∅→
    (∀ e∈E₀,markedStarResource T W e)→E₀.filter (markedInnerResource T W)=∅→
    (∀ j x y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) j x y=1→
      ¬(KR⊔ER).Adj x (if j then π y else y)→
      markedStarResource T W (Sum.inl ({x,if j then π y else y}:Finset V))→
      Sum.inl ({x,if j then π y else y}:Finset V)∈FD)→
    (∀ j x u,H j x u→¬(KS⊔ES).Adj (Sum.inl x) (Sum.inr u)→
      markedStarResource T W (Sum.inr (x,u))→Sum.inr (x,u)∈FD)→
    let FU:=(MA.biUnion markedWheelPhysicalResources).image (markedResourceEmbedding f.toEmbedding g);
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
          ((FU.filter (markedInnerResource (I\T) (J\W))).filter p).card :=by
  intro E K tail head ktail khead S hdiv ME MD hME hMD FE FD ER DR ES DS hMDR hMDS
    DRtot DStot hDRtot hDStot MA hMA σA HA EA KA hArcs hSpokes E₀ hE hD hstar hdeep hdeepR hdeepS FU
  obtain ⟨MU,hMUres,hMU,hMUR,hMUS,hU,hactiveR,hactiveS⟩:=marked_active_cover_packing_lift
    f g P π ρ hf d m σ H DRtot DStot I T J W hfX hgX X Z hX hZ MA hMA hArcs hSpokes
  rw [hDRtot] at hMUR hactiveR
  rw [hDStot] at hMUS hactiveS
  obtain ⟨N,hN,hNres,hrest⟩:=marked_protected_three_stage_completion P π d m hd hm σ H hH I T J W hI hT
    KR KS hKR hKS hdiv ME MD MU hME hMD hMU hMDR hMDS hMUR hMUS E₀ hE hD hU hstar hdeep
    hdeepR hdeepS hactiveR hactiveS
  refine ⟨N,hN,?_,?_⟩
  · rw [hNres,hMUres]
  · simpa only [hMUres] using hrest

end Oberwolfach
