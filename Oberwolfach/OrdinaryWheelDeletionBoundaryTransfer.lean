module

public import Oberwolfach.OrdinaryBalancedDeletionBoundaryTransfer

@[expose] public section
/-! A decomposed wheel deletion preserves inner near-balance up to its
boundary discrepancy, independently of its total deletion degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_wheel_deletion_boundary_transfer
    (Q R:SimpleGraph V) (H E:V→U→Prop) (I:Finset V) (J:Finset U) (r:ℕ) (b d:ℝ)
    (hRQ:R≤Q) (hEH:∀v u,E v u→H v u) (hdec:HasOrdinaryWheelDecomposition R E r)
    (hparent:∀v,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b)
    (hboundary:∀v,|((R\spanningRestriction R I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>E v u∧¬(v∈I∧u∈J))).card|≤d):
    ∀v,|((spanningRestriction (Q\R) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧¬E v u∧v∈I∧u∈J)).card|≤b+d :=by
  obtain ⟨hR,_⟩:=ordinary_wheel_decomposition_balance R E r hdec
  have hfull:∀v,|(R.degree v:ℝ)-2*(Finset.univ.filter (E v)).card|≤0:=by
    intro v
    have hh:((R.degree v:ℝ))=2*(Finset.univ.filter (E v)).card:=by exact_mod_cast hR v
    rw [hh];norm_num
  have hh:=ordinary_balanced_deletion_boundary_transfer Q R H E I J b 0 d hRQ hEH hparent hfull hboundary
  intro v
  convert hh v using 1 <;> simp
end Oberwolfach
