module

public import Oberwolfach.MarkedReservedStarActiveRestriction
public import Oberwolfach.MarkedPhysicalDeletionComposition
public import Oberwolfach.MarkedActiveTotalDeletionBounds

@[expose] public section

/-! On the active pair the temporary reserved star deletes nothing. The
actual successive deletions equal deletion of the two packing graphs;
the latter have the stated physical degree bounds on the active pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U VA UA Γ Color E K:Type} [Fintype V] [Fintype U] [Fintype VA] [Fintype UA]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder VA] [DecidableEq U] [DecidableEq UA]
  {tail head:E→V} {ktail khead:K→V} {πD:Equiv.Perm V} {mD bD:ℕ} {H₀ HK:V→U→Prop}

theorem marked_protected_active_deletion
    (f:VA↪oV) (g:UA↪U) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (I T:Finset V) (J W:Finset U) (hT:∀ v,π v∈T↔v∈T)
    (hf:∀ x,f x∉T) (hg:∀ u,g u∉W)
    (MD:Finset (MarkedWheel tail head ktail khead mD πD bD H₀ HK))
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\W))=∅)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U)) (eR eS cR cV cU:ℝ)
    (heR:∀ x,(ER.degree x:ℝ)≤eR) (heS:∀ z,(ES.degree z:ℝ)≤eS)
    (hcR:0≤cR) (hcV:0≤cV)
    (hR:∀ x∉I,((markedPackingRimGraph MD).degree x:ℝ)≤cR)
    (hV:∀ x∉I,((Finset.univ.filter (markedPackingSpokes MD x)).card:ℝ)≤cV)
    (hU:∀ u∉W,((Finset.univ.filter (fun x=>markedPackingSpokes MD x u)).card:ℝ)≤cU):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    ∀ (KA:Finset (E₀⊕E₁)) (KS:Finset (V×U)),
    (∀ a∈KA,Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a∈T∨
      Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a∈T)→
    (∀ z∈KS,z.1∈T∨z.2∈W)→
    let KR:=markedSampleArcSetGraph P π d σ KA
    let KSg:=markedFiniteSpokeGraph KS
    let DR:=ER⊔markedPackingRimGraph MD
    let DS:=ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs);
    rawMarkedRestrictPair f g (rawMarkedDeleteRims (rawMarkedDeleteRims σ (KR⊔ER).edgeFinset)
      (markedPackingRimGraph MD).edgeFinset)=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset) ∧
    (fun j x u=>markedDeletePhysicalSpokes (markedDeletePhysicalSpokes H (KSg⊔ES))
      (markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) j (f x) (g u))=
      (fun j x u=>markedDeletePhysicalSpokes H DS j (f x) (g u))∧
    (∀ x,((DR.comap f).degree x:ℝ)≤eR+cR)∧
    (∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤eS+cV)∧
    (∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤eS+cU):=by
  intro E₀ E₁ KA KS hKA hKS KR KSg DR DS
  obtain ⟨hKR,hKSg⟩:=marked_reserved_star_active_graphs P π d σ T W hT f g hf hg KA KS hKA hKS
  have hactive:=rawMarked_active_reservation_deletion f g σ H KR DR KSg DS hKR hKSg
  have hdegrees:=marked_active_total_deletion_bounds MD I T J W hstar f.toEmbedding g hf hg
    ER ES eR eS cR cV cU heR heS hcR hcV hR hV hU
  refine ⟨?_,?_,hdegrees⟩
  · have hd:=rawMarkedDeleteRims_sup σ (KR⊔ER) (markedPackingRimGraph MD)
    have hd':rawMarkedDeleteRims (rawMarkedDeleteRims σ (KR⊔ER).edgeFinset) (markedPackingRimGraph MD).edgeFinset=
        rawMarkedDeleteRims σ ((KR⊔ER)⊔markedPackingRimGraph MD).edgeFinset:=by
      convert hd using 1 <;> congr!
    rw [hd']
    have he:((KR⊔ER)⊔markedPackingRimGraph MD).edgeFinset=(KR⊔DR).edgeFinset:=by
      ext e
      simp only [SimpleGraph.mem_edgeFinset]
      rw [sup_assoc]
    rw [he]
    convert hactive.1 using 1 <;> congr!
  · rw [markedDeletePhysicalSpokes_sup]
    have he:(KSg⊔ES)⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)=KSg⊔DS:=sup_assoc _ _ _
    rw [he]
    exact hactive.2

end Oberwolfach
