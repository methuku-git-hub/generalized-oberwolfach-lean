module

public import Oberwolfach.RawIntervalActualReservedMatching
public import Oberwolfach.RetainedMarkedSpokeChanges
public import Oberwolfach.ActualReservedMatchingOuterSlack

@[expose] public section
/-! Trimming interval starts does not delete an ordinary spoke: an ordinary
label was unblocked before trimming and remains unblocked afterwards. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem raw_ordinary_spoke_survives_start_retention
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (g:Γ) (j:Color) (v:V) (u:U)
    (h:rawMarkedSpokes π d σ g j false v u):
    retainedRawMarkedSpokes π d σ g₀ t J g j false v u:=by
  have hraw:rawIntervalState π d (fun e=>σ (u,e)) v=some (Sum.inr j):=h
  have hnot:¬rawIntervalBlocked π d (fun e=>σ (u,e)) v:=
    ((rawIntervalState_label_iff π d (fun e=>σ (u,e)) v j).mp hraw).1
  have heq:=retainedIntervalState_eq_of_no_deletion π d (fun e=>σ (u,e))
    (retainedRawStart π d σ g₀ t J u) (fun _ _ h=>h.1) v
    (by intro a k ha hv;exfalso;exact hnot ⟨k,a,ha,hv⟩)
  change retainedIntervalState π d (fun e=>σ (u,e)) (retainedRawStart π d σ g₀ t J u) v=some (Sum.inr j)
  rw [heq]
  exact hraw

theorem raw_ordinary_outer_subset_retained
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (g:Γ) (j:Color) (u:U):
    rawIntervalOrdinaryOuter π d σ j u⊆
      Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ g₀ t J g j false v u):=by
  intro v hv
  simp only [rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
  exact raw_ordinary_spoke_survives_start_retention π d σ g₀ t J g j v u hv

theorem raw_reserved_matching_event_retained_pairs
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (g:Γ) (j:Color) (α:ℝ)
    (h:rawIntervalReservedMatchingEvent π d σ j α):
    let Outer:=fun u=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ g₀ t J g j false v u);
    ∀x y:V,x≠y→2*α*Fintype.card V≤
      ((((Finset.univ:Finset U).filter (fun u=>x∈Outer u))∩
        ((Finset.univ:Finset U).filter (fun u=>y∈Outer u))).card:ℝ):=by
  intro Outer x y hxy
  have hbase:=h.1 x y hxy
  have hsub:((Finset.univ:Finset U).filter (fun u=>x∈rawIntervalOrdinaryOuter π d σ j u))∩
        ((Finset.univ:Finset U).filter (fun u=>y∈rawIntervalOrdinaryOuter π d σ j u))⊆
      ((Finset.univ:Finset U).filter (fun u=>x∈Outer u))∩
        ((Finset.univ:Finset U).filter (fun u=>y∈Outer u)):=by
    intro u hu
    simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
    exact ⟨raw_ordinary_outer_subset_retained π d σ g₀ t J g j u hu.1,
      raw_ordinary_outer_subset_retained π d σ g₀ t J g j u hu.2⟩
  have hh:(((((Finset.univ:Finset U).filter (fun u=>x∈rawIntervalOrdinaryOuter π d σ j u))∩
        ((Finset.univ:Finset U).filter (fun u=>y∈rawIntervalOrdinaryOuter π d σ j u))).card):ℝ)≤
      (((((Finset.univ:Finset U).filter (fun u=>x∈Outer u))∩
        ((Finset.univ:Finset U).filter (fun u=>y∈Outer u))).card):ℝ):=by exact_mod_cast Finset.card_le_card hsub
  exact hbase.trans hh

theorem raw_reserved_matching_event_retained_lists
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (g:Γ) (j:Color) (α:ℝ) (h:rawIntervalReservedMatchingEvent π d σ j α):
    let Outer:=fun u=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ g₀ t J g j false v u);
    ∀ (C:Finset (Finset V⊕(V×U))) (Hold:Bool→V→U→Prop) (Inner:Finset U)
      (K:SimpleGraph V) (Old:U→Finset V) (Bad:V→Finset U),
      (Inner.card:ℝ)+2*C.card≤α*Fintype.card V→
      (∀u,Disjoint (Old u) (Outer u))→
      let S:=fun e=>commonOuterPairIndices Outer e\Inner;
      let A:=actualReservedOrdinarySpokeLabels C Hold;
      let L:=reservedSpokeMatchingList S A;
      (∀e∈K.edgeFinset,α*Fintype.card V≤((L e).card:ℝ)) ∧
      (∀e∈K.edgeFinset,Disjoint (L e) Inner) ∧
      (∀u e v,e∈K.edgeFinset→v∈e.toFinset→v∈Old u→u∈L e→u∈Bad v) ∧
      (∀e∈K.edgeFinset,∀v∈e.toFinset,∀u∈L e,v∉A u):=by
  intro Outer C Hold Inner K Old Bad hLoss hOld
  have hPairs:=raw_reserved_matching_event_retained_pairs π d σ g₀ t J g j α h
  have hCommon:=actual_common_outer_pair_slack_from_codegrees C Outer Inner K α hPairs hLoss
  have hLists:=actual_outer_pair_lists_from_common_slack C Outer Inner K α hCommon
  exact actual_reserved_matching_inputs_from_outer_slack C Hold
    (fun e=>commonOuterPairIndices Outer e\Inner) K Inner Old Outer Bad α hLists.2.2 hLists.1 hLists.2.1 hOld

end Oberwolfach
