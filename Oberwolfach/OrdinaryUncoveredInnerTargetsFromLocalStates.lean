module

public import Oberwolfach.OrdinaryInnerSpokeTargets
public import Oberwolfach.InnerRequiredRawCount
public import Oberwolfach.InnerRequiredApproximateOccupied

@[expose] public section

/-! Only uncovered targets, rather than the full inner set, are charged to
the placement capacity. The occupancy hypotheses are explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uncovered_inner_targets_from_local_states
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (Inner:Finset V) (Hubs:Finset U) (Old Unused:U→Finset V)
    (hno:∀w x,¬rawIntervalColouredStart π d (fun e=>σ (w,e)) x false)
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈Old w)
    (hordinary:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inr true)→x∈Old w ∨ x∈Unused w):
    ∀w,(((ordinaryInnerSpokeTargets Inner Hubs
      (fun v u=>v∈rawReservedSpokeList π d σ u) w)\Old w).card:ℝ)≤
      rawIntervalUnassignedHubCountOn π d σ w Inner+((Unused w∩Inner).card:ℝ) :=by
  intro w
  let T:=ordinaryInnerSpokeTargets Inner Hubs (fun v u=>v∈rawReservedSpokeList π d σ u) w\Old w
  have hcover:T⊆(rawUnassignedAt π d σ w∩Inner)∪(Unused w∩Inner):=by
    intro x hx
    by_cases hw:w∈Hubs
    · have hT:x∈Inner ∧ x∉rawReservedSpokeList π d σ w ∧ x∉Old w:=by
        simpa [T,ordinaryInnerSpokeTargets,hw,and_assoc] using hx
      cases hs:rawIntervalFamilyState π d σ (x,w) with
      | none =>
        exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨by simp [rawUnassignedAt,hs],hT.1⟩)
      | some y =>
        cases y with
        | inl g =>
          cases g with
          | false =>
            have hc:rawIntervalCovered π d (fun e=>σ (w,e)) x false:=
              (rawIntervalState_interval_iff π d (fun e=>σ (w,e)) x false).mp hs
            obtain ⟨a,ha,_⟩:=hc
            exact (hno w a ha).elim
          | true => exact (hT.2.2 (happrox w x hs)).elim
        | inr j =>
          cases j with
          | false =>
            have hm:x∈rawReservedSpokeList π d σ w:=by simp [rawReservedSpokeList,rawIntervalOrdinaryOuter,hs]
            exact (hT.2.1 hm).elim
          | true =>
            rcases hordinary w x hs with ho|hu
            · exact (hT.2.2 ho).elim
            · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu,hT.1⟩)
    · simp [T,ordinaryInnerSpokeTargets,hw] at hx
  have hc:=Finset.card_le_card hcover
  have hu:=Finset.card_union_le (rawUnassignedAt π d σ w∩Inner) (Unused w∩Inner)
  have hr:((T.card:ℝ))≤((rawUnassignedAt π d σ w∩Inner).card:ℝ)+((Unused w∩Inner).card:ℝ):=by
    exact_mod_cast hc.trans hu
  rw [raw_unassigned_restricted_count_card] at hr
  exact hr
end Oberwolfach
