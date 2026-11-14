module

public import Oberwolfach.OrdinaryDecomposedProtectedTrace

@[expose] public section
/-! A named witness keeps the protected trace, wheel decompositions and
recent-window discrepancy bounds attached to one deletion history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryProtectedWindowBalanceHistory
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (r n:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (I Parent:Finset V) (J:Finset U) (window:Finset ℕ) (inner cross:ℕ→ℝ):Type where
  rim:ℕ→SimpleGraph V
  spokes:ℕ→V→U→Prop
  state:ordinaryHostResources (ordinaryHistoryRim Q rim spokes n) (ordinaryHistorySpokes H rim spokes n)=A
  root:n=0 ∨ A⊆ordinaryRootResources (X (n-1)) (Z (n-1))
  levels:∀i<n,
    (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (rim i) (spokes i))
      (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤cost i) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph (rim i) (spokes i) (T i) (W i))
      (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤deepCost i) ∧
    Disjoint (ordinaryPhysicalGraph (rim i) (spokes i)) (ordinaryDeepBlocker (T i) (W i))
  decomposition:∀i<n,rim i≤ordinaryHistoryRim Q rim spokes i ∧
    (∀v u,spokes i v u→ ordinaryHistorySpokes H rim spokes i v u) ∧
    HasOrdinaryWheelDecomposition (rim i) (spokes i) r
  inner_boundary:∀i∈window,∀v∈I,|(((rim i)\spanningRestriction (rim i) I).degree v:ℝ)-
    2*(Finset.univ.filter (fun u=>spokes i v u∧¬(v∈I∧u∈J))).card|≤ inner i
  cross_boundary:∀i∈window,∀v∈Parent,v∉I→
    |(((rim i).neighborFinset v∩I).card:ℝ)-2*(J.filter (spokes i v)).card|≤ cross i

theorem ordinary_protected_window_balance_history_forget
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (r n:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (I Parent:Finset V) (J:Finset U) (window:Finset ℕ) (inner cross:ℕ→ℝ)
    (h:OrdinaryProtectedWindowBalanceHistory Q H X T Z W cost deepCost r n A I Parent J window inner cross):
    OrdinaryDecomposedProtectedTrace Q H X T Z W cost deepCost r n A :=by
  exact ⟨h.rim,h.spokes,h.state,h.root,h.levels,h.decomposition⟩
end Oberwolfach
