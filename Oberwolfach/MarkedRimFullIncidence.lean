module

public import Oberwolfach.MarkedModifiedPhysicalIncidence

@[expose] public section
/-! A physical change graph controls the typed incidences even if edges are
added, removed, reversed or retyped. No sampling is involved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_rim_physical_change_incidence
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (τ:RawMarkedOutcome V U Γ Color) (DR:SimpleGraph V)
    (hchange:∀ a, ¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a) →
      markedPairPhysical π a∈DR.edgeFinset) (delta:ℝ) (hD:∀ x,(DR.degree x:ℝ)≤delta):
    let R:=rawMarkedPairRims P π d σ
    let R':=rawMarkedPairRims P π d τ
    (∀ x,(∑ e:(V×V)⊕(V×V),if ¬(R e↔R' e) ∧ Sum.elim Prod.fst Prod.fst e=x then (1:ℝ) else 0)≤2*delta) ∧
    (∀ x,(∑ e:(V×V)⊕(V×V),if ¬(R e↔R' e) ∧ Sum.elim Prod.snd Prod.snd e=x then (1:ℝ) else 0)≤2*delta):=by
  dsimp only
  have hh (mark incoming:Bool) (x:V):=
    (marked_row_rim_physical_change P π d σ τ DR hchange mark incoming x).trans (hD _)
  constructor
  · intro x
    have h0:=hh false false x
    have h1:=hh true false x
    calc
      _ ≤ delta+delta:=by
        rw [Fintype.sum_sum_type]
        apply add_le_add
        · convert h0 using 1
          convert pair_indicator_sum_at_first
            (fun e=>¬(rawMarkedPairRims P π d σ (Sum.inl e)↔
              rawMarkedPairRims P π d τ (Sum.inl e))) x using 1 <;>
            (apply Finset.sum_congr rfl
             intro z _
             simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]
             split_ifs <;> simp_all)
        · convert h1 using 1
          convert pair_indicator_sum_at_first
            (fun e=>¬(rawMarkedPairRims P π d σ (Sum.inr e)↔
              rawMarkedPairRims P π d τ (Sum.inr e))) x using 1 <;>
            (apply Finset.sum_congr rfl
             intro z _
             simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]
             split_ifs <;> simp_all)
      _ = _:=by ring
  · intro x
    have h0:=hh false true x
    have h1:=hh true true x
    calc
      _ ≤ delta+delta:=by
        rw [Fintype.sum_sum_type]
        apply add_le_add
        · convert h0 using 1
          convert pair_indicator_sum_at_second
            (fun e=>¬(rawMarkedPairRims P π d σ (Sum.inl e)↔
              rawMarkedPairRims P π d τ (Sum.inl e))) x using 1 <;>
            (apply Finset.sum_congr rfl
             intro z _
             simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]
             split_ifs <;> simp_all)
        · convert h1 using 1
          convert pair_indicator_sum_at_second
            (fun e=>¬(rawMarkedPairRims P π d σ (Sum.inr e)↔
              rawMarkedPairRims P π d τ (Sum.inr e))) x using 1 <;>
            (apply Finset.sum_congr rfl
             intro z _
             simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]
             split_ifs <;> simp_all)
      _ = _:=by ring

end Oberwolfach
