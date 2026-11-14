module

public import Oberwolfach.MarkedBalanceSpokeChanges

@[expose] public section
/-! The full-domain reference balance gives the row and column size
estimates required for the physical spoke-change graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_full_spoke_balance
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (ε:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (h:MarkedRestrictedBalanceWithSpokes P π d m Finset.univ Finset.univ ε σ H):
    (∀v,|((markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) false true v Finset.univ:ℝ)+
         (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) true true v Finset.univ:ℝ))-
       (((Finset.univ.filter (fun u=>H false v u)).card:ℝ)+((Finset.univ.filter (fun u=>H true v u)).card:ℝ))|≤ε) ∧
    (∀u,|((Finset.univ.filter (fun v=>H false v u)).card:ℝ)-(m:ℝ)*((Finset.univ.filter (fun v=>H true v u)).card:ℝ)|≤ε):=by
  constructor
  · intro v
    have hh:=(h.1 v).1 true
    simpa only [Finset.sum_boole,bipAdj] using hh
  · intro u
    have hh:=h.2 u
    simpa only [Finset.sum_boole,bipAdj] using hh
end Oberwolfach
