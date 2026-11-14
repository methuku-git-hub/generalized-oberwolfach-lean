module

public import Oberwolfach.OrdinaryAvoidingWheelBoundaryBalance

@[expose] public section
/-! Only deletions that do not protect the present inner pair contribute
boundary imbalance to the actual host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_actual_trace_window_boundary_balance
    (Q G:SimpleGraph V) (H Hs:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop)
    (A:Finset (Sym2 V⊕(V×U))) (I:Finset V) (J:Finset U) (window:Finset ℕ) (r n:ℕ) (b:ℝ) (boundary:ℕ→ℝ)
    (hwindow:∀i∈window,i<n)
    (hhist:ordinaryHostResources (ordinaryHistoryRim Q R S n) (ordinaryHistorySpokes H R S n)=A)
    (hstate:ordinaryHostResources G Hs=A)
    (hinit:∀v∈I,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b)
    (hsub:∀i<n,R i≤ordinaryHistoryRim Q R S i ∧ ∀v u,S i v u→ ordinaryHistorySpokes H R S i v u)
    (hdec:∀i<n,HasOrdinaryWheelDecomposition (R i) (S i) r)
    (havoid:∀i<n,i∉window→Disjoint (ordinaryPhysicalGraph (R i) (S i)) (ordinaryDeepBlocker I J))
    (hboundary:∀i∈window,∀v∈I,|(((R i)\spanningRestriction (R i) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>S i v u∧¬(v∈I∧u∈J))).card|≤boundary i):
    ∀v∈I,|((spanningRestriction G I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>Hs v u∧v∈I∧u∈J)).card|≤b+∑j∈window,boundary j :=by
  let costs:=fun i=>if i∈window then boundary i else 0
  have hb:∀i<n,∀v∈I,|(((R i)\spanningRestriction (R i) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>S i v u∧¬(v∈I∧u∈J))).card|≤costs i:=by
    intro i hi v hv
    by_cases hw:i∈window
    · simpa [costs,hw] using hboundary i hw v hv
    · simpa [costs,hw] using ordinary_avoiding_wheel_boundary_balance (R i) (S i) I J r (hdec i hi) (havoid i hi hw) v
  have hh:=ordinary_actual_trace_boundary_balance Q G H Hs R S A I J r n b costs hhist hstate hinit hsub hdec hb
  have hfilter:(Finset.range n).filter (fun i=>i∈window)=window:=by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    constructor
    · exact And.right
    · intro hi;exact ⟨hwindow i hi,hi⟩
  have hsum:(∑i∈Finset.range n,costs i)=∑i∈window,boundary i:=by
    dsimp [costs]
    rw [←Finset.sum_filter,hfilter]
  intro v hv
  have hresult:=hh v hv
  rw [hsum] at hresult
  exact hresult
end Oberwolfach
