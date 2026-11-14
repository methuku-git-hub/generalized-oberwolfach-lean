module

public import Oberwolfach.OrdinaryUncoveredTargetsFromUnmatchedRows
public import Oberwolfach.InnerRequiredRawOccurrence

@[expose] public section

/-! At a fixed vertex, only unassigned states and unused true spokes can
contribute to the column of uncovered inner targets. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uncovered_target_column_from_states
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (Inner:Finset V) (Hubs:Finset U) (Old:U→Finset V)
    (hno:∀w x,¬rawIntervalColouredStart π d (fun e=>σ (w,e)) x false)
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈Old w):
    ∀v,(((Finset.univ:Finset U).filter (fun w=>v∈
      ordinaryInnerSpokeTargets Inner Hubs (fun x u=>x∈rawReservedSpokeList π d σ u) w\Old w)).card:ℝ)≤
      rawIntervalUnassignedColumnCount π d σ v Hubs+
        (((Finset.univ:Finset U).filter (fun w=>v∈ordinaryUnusedTrueSpokes π d σ Old w)).card:ℝ) :=by
  intro v
  let C:=Hubs.filter (fun w=>v∈rawUnassignedAt π d σ w)
  let T:=(Finset.univ:Finset U).filter (fun w=>v∈ordinaryUnusedTrueSpokes π d σ Old w)
  have hsub:(Finset.univ.filter (fun w=>v∈
      ordinaryInnerSpokeTargets Inner Hubs (fun x u=>x∈rawReservedSpokeList π d σ u) w\Old w))⊆C∪T:=by
    intro w hw
    have ht: v∈ordinaryInnerSpokeTargets Inner Hubs (fun x u=>x∈rawReservedSpokeList π d σ u) w\Old w:=
      (Finset.mem_filter.mp hw).2
    by_cases hHub:w∈Hubs
    · have hv:v∈Inner ∧ v∉rawReservedSpokeList π d σ w ∧ v∉Old w:=by
        simpa [ordinaryInnerSpokeTargets,hHub,and_assoc] using ht
      cases hs:rawIntervalFamilyState π d σ (v,w) with
      | none =>
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hHub,by simp [rawUnassignedAt,hs]⟩)
      | some y =>
        cases y with
        | inl g =>
          cases g with
          | false =>
            have hc:rawIntervalCovered π d (fun e=>σ (w,e)) v false:=
              (rawIntervalState_interval_iff π d (fun e=>σ (w,e)) v false).mp hs
            obtain ⟨x,hx,_⟩:=hc
            exact (hno w x hx).elim
          | true => exact (hv.2.2 (happrox w v hs)).elim
        | inr j =>
          cases j with
          | false =>
            have hm:v∈rawReservedSpokeList π d σ w:=by simp [rawReservedSpokeList,rawIntervalOrdinaryOuter,hs]
            exact (hv.2.1 hm).elim
          | true =>
            apply Finset.mem_union_right
            simp [T,ordinaryUnusedTrueSpokes,hs,hv.2.2]
    · simp [ordinaryInnerSpokeTargets,hHub] at ht
  have hc:=Finset.card_le_card hsub
  have hu:=Finset.card_union_le C T
  have hb:((Finset.univ.filter (fun w=>v∈
      ordinaryInnerSpokeTargets Inner Hubs (fun x u=>x∈rawReservedSpokeList π d σ u) w\Old w)).card:ℝ)≤(C.card:ℝ)+T.card:=by
    exact_mod_cast hc.trans hu
  rw [show (C.card:ℝ)=rawIntervalUnassignedColumnCount π d σ v Hubs from
    raw_unassigned_restricted_column_card π d σ v Hubs] at hb
  exact hb
end Oberwolfach
