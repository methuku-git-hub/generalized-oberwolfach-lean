module

public import Oberwolfach.OrdinaryProtectedTraceInvariant

@[expose] public section
/-! Recover the next boundary edit estimate directly from the invariant and
actual host resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_trace_boundary_edit
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G Hs=A)
    (hX:∀j < i,X i⊆T j) (hZ:∀j < i,Z i⊆W j):
    let B:=spanningRestriction (ordinaryBoundaryGraph Q H (T i) (W i)) (ordinaryInnerVertices (X i) (Z i));
    let B':=spanningRestriction (ordinaryBoundaryGraph G Hs (T i) (W i)) (ordinaryInnerVertices (X i) (Z i));
    ∀w:V⊕U,((changed (B.neighborFinset w) (B'.neighborFinset w)).card:ℝ)≤deepCost i:=by
  intro B B'
  obtain ⟨R,S,hist,_,hlevels⟩:=htrace
  obtain ⟨hG,hH⟩:=ordinaryHostResources_injective G (ordinaryHistoryRim Q R S (i+1)) Hs
    (ordinaryHistorySpokes H R S (i+1)) (hstate.trans hist.symm)
  subst G
  subst Hs
  have hcost:∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph (R i) (S i) (T i) (W i))
      (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤deepCost i:=(hlevels i (by omega)).2.1
  have havoid:∀j < i,Disjoint (ordinaryPhysicalGraph (R j) (S j)) (ordinaryDeepBlocker (T j) (W j)):=by
    intro j hj
    exact (hlevels j (by omega)).2.2
  have hh:=ordinary_deletion_history_boundary_edit Q H R S i (X i) (T i) (Z i) (W i) T W (deepCost i)
    hX hZ havoid hcost
  intro w
  convert hh w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
