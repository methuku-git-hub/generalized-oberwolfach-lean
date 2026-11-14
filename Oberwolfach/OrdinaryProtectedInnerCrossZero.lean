module

public import Oberwolfach.OrdinaryProtectedInnerPersistence
public import Oberwolfach.OrdinaryCrossBalanceDeletionTransferAt

@[expose] public section
/-! An earlier deletion protecting a deeper pair has small cross discrepancy
whenever its recorded deep-boundary degree is small. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_inner_cross_zero
    (R:SimpleGraph V) (S:V→U→Prop) (T I:Finset V) (W J:Finset U)
    (hIT:I⊆T) (hJW:J⊆W) (v:V) (hvT:v∈T)
    (havoid:Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W)):
    |((R.neighborFinset v∩I).card:ℝ)-2*(J.filter (S v)).card|=0 :=by
  have hz:=ordinary_protected_inner_zero R S T W havoid
  have hrim:R.neighborFinset v∩I=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxR:(R.Adj v x):=(R.mem_neighborFinset v x).mp (Finset.mem_inter.mp hx).1
    have hxT:x∈T:=hIT (Finset.mem_inter.mp hx).2
    have hh:(spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices T W)).Adj (Sum.inl v) (Sum.inl x):=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hxR,(ordinaryInnerVertices_left T W v).mpr hvT,(ordinaryInnerVertices_left T W x).mpr hxT⟩
    rw [hz] at hh
    exact hh
  have hsp:J.filter (S v)=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have huW:u∈W:=hJW (Finset.mem_filter.mp hu).1
    have huS:S v u:=(Finset.mem_filter.mp hu).2
    have hh:(spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices T W)).Adj (Sum.inl v) (Sum.inr u):=
      (spanningRestriction_adj _ _ _ _).mpr ⟨huS,(ordinaryInnerVertices_left T W v).mpr hvT,(ordinaryInnerVertices_right T W u).mpr huW⟩
    rw [hz] at hh
    exact hh
  simp only [hrim,hsp,Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero,abs_zero]
end Oberwolfach
