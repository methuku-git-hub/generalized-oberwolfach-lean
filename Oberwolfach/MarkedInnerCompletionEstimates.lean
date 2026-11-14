module

public import Oberwolfach.MarkedInnerDeletionBudgets
public import Oberwolfach.MarkedReservedStarActiveRestriction
public import Oberwolfach.MarkedConfigurationsAfterPhysicalDeletionOnDomain
public import Oberwolfach.MarkedDomainSpokeLoadsAfterDeletion

@[expose] public section

/-! Inner completion inputs after both constructed packings. Deep wheels
avoid the inner star, so all inner configuration and fixed weighted-load
losses are charged solely to the prescribed-edge deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π₀:Equiv.Perm V} {m₀ b₀:ℕ} {H₀ HK:V→U→Prop}

theorem marked_inner_configurations_after_both_packings
    (MD:Finset (MarkedWheel tail head ktail khead m₀ π₀ b₀ H₀ HK)) (A:Finset V) (B:Finset U)
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource A B)=∅)
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hA:∀ x,π x∈A↔x∈A)
    (βC βP zetaR zetaS:ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hc:MarkedLocalConfigurationsWithSpokes r P π d A βC βP σ H)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U))
    (hR:∀ x,(ER.degree x:ℝ)≤zetaR*A.card)
    (hS:∀ u,((A.filter (fun x=>ES.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤zetaS*A.card):
    MarkedLocalConfigurationsWithSpokes r P π d A
      (βC-(r+5:ℕ)*(zetaR+zetaS)) (βP-(r+7:ℕ)*zetaR-(r+4:ℕ)*zetaS)
      (rawMarkedDeleteRims σ (ER⊔markedPackingRimGraph MD).edgeFinset)
      (markedDeletePhysicalSpokes H (ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs))):=by
  have hi:=marked_inner_deletion_has_only_prescribed_cost MD A B hstar ER ES
  have hr: ∀ x, (((ER⊔markedPackingRimGraph MD).neighborFinset x∩A).card:ℝ)≤zetaR*A.card := by
    intro x
    rw [hi.1 x]
    exact (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)).trans
      (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hR x)
  have hs: ∀ u, ((A.filter (fun x=>(ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤zetaS*A.card := by
    intro u
    have he:A.filter (fun x=>(ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).Adj (Sum.inl x) (Sum.inr u))=
        A.filter (fun x=>ES.Adj (Sum.inl x) (Sum.inr u)):=by
      ext x
      simp only [Finset.mem_filter,SimpleGraph.sup_adj]
      constructor
      · rintro ⟨hx,hE|hD⟩
        · exact ⟨hx,hE⟩
        · exact ((marked_deep_spoke_graph_avoids_inner MD A B hstar).1 (Sum.inr u) x hx hD.symm).elim
      · rintro ⟨hx,hE⟩;exact ⟨hx,Or.inl hE⟩
    rw [he]
    exact hS u
  have hh := marked_local_configurations_after_physical_deletion_on_domain r P π d A hA βC βP zetaR zetaS σ H hc
    (ER⊔markedPackingRimGraph MD) (ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs))
    (by
      intro x
      simpa only [←Set.ncard_coe_finset, Finset.coe_inter, SimpleGraph.coe_neighborFinset] using hr x)
    (by
      intro u
      simpa only [←Set.ncard_coe_finset, Finset.coe_filter] using hs u)
  have hedge : @SimpleGraph.edgeFinset V (ER⊔markedPackingRimGraph MD)
      (@SimpleGraph.fintypeEdgeSet V (ER⊔markedPackingRimGraph MD) inferInstance
        (fun a b=>Classical.propDecidable ((ER⊔markedPackingRimGraph MD).Adj a b))) =
      (ER⊔markedPackingRimGraph MD).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  rw [hedge] at hh
  exact hh

variable {V₀ U₀:Type} [Fintype V₀] [Fintype U₀] [LinearOrder V₀] [DecidableEq U₀]

theorem marked_inner_domain_restriction_ignores_deep_packing
    (MD:Finset (MarkedWheel tail head ktail khead m₀ π₀ b₀ H₀ HK)) (A:Finset V) (B:Finset U)
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource A B)=∅)
    (f:V₀→V) (g:U₀→U) (hf:∀ x,f x∈A)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U)):
    rawMarkedRestrictPair f g (rawMarkedDeleteRims σ (ER⊔markedPackingRimGraph MD).edgeFinset)=
      rawMarkedRestrictPair f g (rawMarkedDeleteRims σ ER.edgeFinset) ∧
    (fun b x u=>markedDeletePhysicalSpokes H (ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) b (f x) (g u))=
      (fun b x u=>markedDeletePhysicalSpokes H ES b (f x) (g u)):=by
  have hs:=marked_deep_spoke_graph_avoids_inner MD A B hstar
  have hR:(markedPackingRimGraph MD).comap f=⊥:=by
    ext x y
    simp only [SimpleGraph.comap_adj,SimpleGraph.bot_adj]
    apply iff_false_intro
    intro hxy
    have hm:f y∈(markedPackingRimGraph MD).neighborFinset (f x)∩A:=
      Finset.mem_inter.mpr ⟨((markedPackingRimGraph MD).mem_neighborFinset _ _).mpr hxy,hf y⟩
    rw [(marked_packing_star_avoidance_neighbours MD A B hstar).1 (f x)] at hm
    exact Finset.notMem_empty _ hm
  have hS:(markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).comap (Sum.map f g)=⊥:=by
    ext x y
    simp only [SimpleGraph.comap_adj,SimpleGraph.bot_adj]
    apply iff_false_intro
    intro hxy
    cases x with
    | inl x=>exact hs.1 (Sum.map f g y) (f x) (hf x) hxy.symm
    | inr u=>cases y with
      | inl y=>exact hs.1 (Sum.inr (g u)) (f y) (hf y) hxy
      | inr v=>exact (markedFiniteSpokeGraph_same_part _).2 (g u) (g v) hxy
  have he:=rawMarked_active_reservation_deletion f g σ H (markedPackingRimGraph MD) ER
    (markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) ES hR hS
  constructor
  · have heq:(ER⊔markedPackingRimGraph MD).edgeFinset=(markedPackingRimGraph MD⊔ER).edgeFinset:=by
      ext e
      simp only [SimpleGraph.mem_edgeFinset]
      rw [sup_comm ER]
    rw [heq]
    exact he.1
  · funext b x u
    apply propext
    have hn:¬(markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)).Adj (Sum.inl (f x)) (Sum.inr (g u)):=
      fun hz=>hs.1 (Sum.inr (g u)) (f x) (hf x) hz.symm
    simp only [markedDeletePhysicalSpokes,SimpleGraph.sup_adj,hn,or_false]

end Oberwolfach
