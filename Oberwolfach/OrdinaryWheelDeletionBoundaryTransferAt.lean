module

public import Oberwolfach.OrdinaryBalancedDeletionBoundaryTransferAt

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

theorem ordinary_wheel_deletion_boundary_transfer_at
    (Q R:SimpleGraph V) (H E:V→U→Prop) (I:Finset V) (J:Finset U) (r:ℕ) (b d:ℝ) (v:V)
    (hRQ:R≤Q) (hEH:∀v u,E v u→H v u) (hdec:HasOrdinaryWheelDecomposition R E r)
    (hparent:|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b)
    (hboundary:|((R\spanningRestriction R I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>E v u∧¬(v∈I∧u∈J))).card|≤d):
    |((spanningRestriction (Q\R) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧¬E v u∧v∈I∧u∈J)).card|≤b+d :=by
  obtain ⟨hR,_⟩:=ordinary_wheel_decomposition_balance R E r hdec
  have hfull:|(R.degree v:ℝ)-2*(Finset.univ.filter (E v)).card|≤0:=by
    have hh:((R.degree v:ℝ))=2*(Finset.univ.filter (E v)).card:=by exact_mod_cast hR v
    rw [hh];norm_num
  have hh:=ordinary_balanced_deletion_boundary_transfer_at Q R H E I J b 0 d v hRQ hEH hparent hfull hboundary
  convert hh using 1 <;> simp
end Oberwolfach
