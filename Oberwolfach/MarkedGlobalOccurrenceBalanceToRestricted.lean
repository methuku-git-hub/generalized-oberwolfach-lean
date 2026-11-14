module

public import Oberwolfach.MarkedFullBalanceFromReferenceTests
public import Oberwolfach.MarkedSampleOccurrenceMatrix
public import Oberwolfach.TypedMatrixRealization

@[expose] public section
/-! The four global occurrence balances are exactly the restricted balance
needed by the correction on the full vertex and hub sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_global_occurrence_balance_to_restricted
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (η:ℝ):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    (∀v,|occurrenceDegree (Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1)) v-
      (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η)→
    (∀v,|occurrenceDegree (Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2)) v-
      (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η)→
    (∀v,|occurrenceDegree (fun e:K=>e.val.2) v-(∑u,if H true v u then (1:ℝ) else 0)|≤η)→
    (∀u,|(∑v,if H false v u then (1:ℝ) else 0)-(m:ℝ)*(∑v,if H true v u then (1:ℝ) else 0)|≤η)→
    MarkedRestrictedBalanceWithSpokes P π d m Finset.univ Finset.univ η σ H :=by
  intro E K hout hin hmarked hcol
  dsimp only [MarkedRestrictedBalanceWithSpokes]
  constructor
  · intro v
    have hE:=markedSampleArc_degrees P π (3*d) (fun e=>σ (Sum.inl e)) false v
    have hK:=markedSampleArc_degrees P π (3*d) (fun e=>σ (Sum.inl e)) true v
    have ho:=hout v
    have hi:=hin v
    have hm:=hmarked v
    rw [occurrenceDegree_sum,hE.1,hK.1] at ho
    rw [occurrenceDegree_sum,hE.2,hK.2] at hi
    rw [hK.2] at hm
    constructor
    · intro incoming
      cases incoming
      · simpa [markedRestrictedDegree,bipAdj,Nat.cast_sum,sub_add_eq_sub_sub] using ho
      · simpa [markedRestrictedDegree,bipAdj,Nat.cast_sum,sub_add_eq_sub_sub] using hi
    · simpa [markedRestrictedDegree,bipAdj,Nat.cast_sum] using hm
  · intro u
    simpa [bipAdj] using hcol u
end Oberwolfach
