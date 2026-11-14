module

public import Oberwolfach.OrdinaryActualTraceBoundaryBalance

@[expose] public section
/-! If each deletion and its boundary part both decompose into wheels, then
the protected inner balance is preserved without any accumulated edit cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_history_boundary_decomposition_balance
    (Q G:SimpleGraph V) (H Hs:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop)
    (A:Finset (Sym2 V⊕(V×U))) (I:Finset V) (J:Finset U) (r n:ℕ) (b:ℝ)
    (hhist:ordinaryHostResources (ordinaryHistoryRim Q R S n) (ordinaryHistorySpokes H R S n)=A)
    (hstate:ordinaryHostResources G Hs=A)
    (hinit:∀v∈I,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b)
    (hsub:∀i<n,R i≤ordinaryHistoryRim Q R S i ∧ ∀v u,S i v u→ ordinaryHistorySpokes H R S i v u)
    (hdec:∀i<n,HasOrdinaryWheelDecomposition (R i) (S i) r)
    (hboundary:∀i<n,HasOrdinaryWheelDecomposition ((R i)\spanningRestriction (R i) I)
      (fun v u=>S i v u∧¬(v∈I∧u∈J)) r):
    ∀v∈I,|((spanningRestriction G I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>Hs v u∧v∈I∧u∈J)).card|≤b :=by
  have hb:∀i<n,∀v∈I,|(((R i)\spanningRestriction (R i) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>S i v u∧¬(v∈I∧u∈J))).card|≤(fun _=>0:ℕ→ℝ) i:=by
    intro i hi v hv
    obtain ⟨hh,_⟩:=ordinary_wheel_decomposition_balance ((R i)\spanningRestriction (R i) I)
      (fun v u=>S i v u∧¬(v∈I∧u∈J)) r (hboundary i hi)
    have hn:((R i)\spanningRestriction (R i) I).degree v=
      2*(Finset.univ.filter (fun u=>S i v u∧¬(v∈I∧u∈J))).card:=by
      convert hh v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have heq:((((R i)\spanningRestriction (R i) I).degree v):ℝ)=
      2*(Finset.univ.filter (fun u=>S i v u∧¬(v∈I∧u∈J))).card:=by exact_mod_cast hn
    rw [heq]
    norm_num
  have hh:=ordinary_actual_trace_boundary_balance Q G H Hs R S A I J r n b (fun _=>0) hhist hstate hinit hsub hdec hb
  intro v hv
  simpa using hh v hv
end Oberwolfach
