module

public import Oberwolfach.MarkedBalanceSpokeChanges

@[expose] public section
/-! Restricted balances on the original fixed domains after simultaneous
rim and spoke changes, with all ambient roots retained. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_restricted_balance_after_arbitrary_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (A:Finset V) (B:Finset U)
    (η δR δS:ℝ) (hR0:0≤δR) (hS0:0≤δS)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hbal:MarkedRestrictedBalanceWithSpokes P π d m A B η σ H)
    (hR:∀ mark incoming x,
      |(markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) mark incoming x A:ℝ)-
        (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming x A:ℝ)|≤δR)
    (hrow:∀ b x,(∑ u∈B,if ¬(H b x u↔H' b x u) then (1:ℝ) else 0)≤δS)
    (hcol:∀ b u,(∑ x∈A,if ¬(H b x u↔H' b x u) then (1:ℝ) else 0)≤δS):
    MarkedRestrictedBalanceWithSpokes P π d m A B (η+2*δR+(m+2:ℕ)*δS) τ H' := by
  have hr (b:Bool) (x:V):
      |(∑ u∈B,bipAdj (H' b) x u)-(∑ u∈B,bipAdj (H b) x u)|≤δS := by
    have hh:=(indicator_sum_change B (fun u=>H b x u) (fun u=>H' b x u)).trans (hrow b x)
    convert hh using 1
    apply congrArg abs
    apply congrArg₂ (fun a b:ℝ=>a-b) <;> apply Finset.sum_congr rfl <;> intro u hu <;> unfold bipAdj <;> split_ifs <;> rfl
  have hc (b:Bool) (u:U):
      |(∑ x∈A,bipAdj (H' b) x u)-(∑ x∈A,bipAdj (H b) x u)|≤δS := by
    have hh:=(indicator_sum_change A (fun x=>H b x u) (fun x=>H' b x u)).trans (hcol b u)
    convert hh using 1
    apply congrArg abs
    apply congrArg₂ (fun a b:ℝ=>a-b) <;> apply Finset.sum_congr rfl <;> intro x hx <;> unfold bipAdj <;> split_ifs <;> rfl
  have hm:(0:ℝ)≤m:=Nat.cast_nonneg _
  constructor
  · intro x
    constructor
    · intro incoming
      have h0:=abs_le.mp (hR false incoming x)
      have h1:=abs_le.mp (hR true incoming x)
      have hs0:=abs_le.mp (hr false x)
      have hs1:=abs_le.mp (hr true x)
      have hb:=abs_le.mp ((hbal.1 x).1 incoming)
      apply abs_le.mpr
      constructor <;> push_cast <;> nlinarith [mul_nonneg hm hS0]
    · have h1:=abs_le.mp (hR true true x)
      have hs1:=abs_le.mp (hr true x)
      have hb:=abs_le.mp ((hbal.1 x).2)
      apply abs_le.mpr
      constructor <;> push_cast <;> nlinarith [mul_nonneg hm hS0]
  · intro u
    have hs0:=abs_le.mp (hc false u)
    have hs1:=abs_le.mp (hc true u)
    have hb:=abs_le.mp (hbal.2 u)
    have hh0:=mul_le_mul_of_nonneg_left hs1.1 hm
    have hh1:=mul_le_mul_of_nonneg_left hs1.2 hm
    apply abs_le.mpr
    constructor <;> push_cast <;> nlinarith [hh0,hh1]
end Oberwolfach
