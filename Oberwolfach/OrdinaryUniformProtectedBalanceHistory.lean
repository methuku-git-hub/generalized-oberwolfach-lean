module

public import Oberwolfach.OrdinaryDecomposedProtectedTraceWitness
public import Oberwolfach.OrdinaryProtectedWindowBalanceHistory

@[expose] public section
/-! One decomposed protected history tracks boundary-discrepancy conditions
for every later target level, so the same history can feed a level chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryWheelInnerBoundaryError (D:SimpleGraph V) (E:V→U→Prop) (I:Finset V) (J:Finset U) (v:V):ℝ :=
  |((D\spanningRestriction D I).degree v:ℝ)-
    2*(Finset.univ.filter (fun u=>E v u∧¬(v∈I∧u∈J))).card|

def ordinaryWheelCrossError (D:SimpleGraph V) (E:V→U→Prop) (I:Finset V) (J:Finset U) (v:V):ℝ :=
  |((D.neighborFinset v∩I).card:ℝ)-2*(J.filter (E v)).card|

structure OrdinaryUniformProtectedBalanceHistory
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (r n L:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (I Parent:ℕ→Finset V) (J:ℕ→Finset U) (window:ℕ→Finset ℕ) (inner cross:ℕ→ℕ→ℝ):Type where
  rim:ℕ→SimpleGraph V
  spokes:ℕ→V→U→Prop
  trace:OrdinaryDecomposedProtectedTraceWitness Q H X T Z W cost deepCost r n A rim spokes
  inner_boundary:∀target<L,∀j<n,j∈window target→∀v∈I target,
    ordinaryWheelInnerBoundaryError (rim j) (spokes j) (I target) (J target) v≤ inner target j
  cross_boundary:∀target<L,∀j<n,j∈window target→∀v∈Parent target,v∉I target→
    ordinaryWheelCrossError (rim j) (spokes j) (I target) (J target) v≤ cross target j

def ordinary_uniform_protected_balance_history_at
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (r n L:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (I Parent:ℕ→Finset V) (J:ℕ→Finset U) (window:ℕ→Finset ℕ) (inner cross:ℕ→ℕ→ℝ)
    (h:OrdinaryUniformProtectedBalanceHistory Q H X T Z W cost deepCost r n L A I Parent J window inner cross)
    (target:ℕ) (ht:target<L) (hwindow:∀j∈window target,j<n):
    OrdinaryProtectedWindowBalanceHistory Q H X T Z W cost deepCost r n A
      (I target) (Parent target) (J target) (window target) (inner target) (cross target) :=by
  refine ⟨h.rim,h.spokes,h.trace.1,h.trace.2.1,h.trace.2.2.1,h.trace.2.2.2,?_,?_⟩
  · intro j hj v hv
    exact h.inner_boundary target ht j (hwindow j hj) hj v hv
  · intro j hj v hv hvout
    exact h.cross_boundary target ht j (hwindow j hj) hj v hv hvout

def ordinary_uniform_protected_balance_history_initial
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (r L:ℕ)
    (I Parent:ℕ→Finset V) (J:ℕ→Finset U) (window:ℕ→Finset ℕ) (inner cross:ℕ→ℕ→ℝ):
    OrdinaryUniformProtectedBalanceHistory Q H X T Z W cost deepCost r 0 L
      (ordinaryHostResources Q H) I Parent J window inner cross :=by
  let R:ℕ→SimpleGraph V:=fun _=>⊥
  let S:ℕ→V→U→Prop:=fun _ _ _=>False
  have htrace:OrdinaryDecomposedProtectedTraceWitness Q H X T Z W cost deepCost r 0
      (ordinaryHostResources Q H) R S:=by
    refine ⟨?_,Or.inl rfl,?_,?_⟩
    · have hq:ordinaryHistoryRim Q R S 0=Q:=by
        ext a b
        simp [ordinaryHistoryRim,ordinaryDeletionHistory]
      have hh:ordinaryHistorySpokes H R S 0=H:=by
        funext v u
        simp [ordinaryHistorySpokes,ordinarySpokesAfterPhysicalDeletion,ordinaryDeletionHistory]
      rw [hq,hh]
    · intro i hi;omega
    · intro i hi;omega
  refine ⟨R,S,htrace,?_,?_⟩
  · intro target ht j hj;omega
  · intro target ht j hj;omega

def ordinary_uniform_protected_balance_history_advance
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (r i L:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (I Parent:ℕ→Finset V) (J:ℕ→Finset U) (window:ℕ→Finset ℕ) (inner cross:ℕ→ℕ→ℝ)
    (h:OrdinaryUniformProtectedBalanceHistory Q H X T Z W cost deepCost r i L A I Parent J window inner cross)
    (G D:SimpleGraph V) (Hs E:V→U→Prop) (hstate:ordinaryHostResources G Hs=A)
    (hD:D≤G) (hE:∀v u,E v u→Hs v u) (hdec:HasOrdinaryWheelDecomposition D E r)
    (hroot:ordinaryHostResources (G\D) (fun v u=>Hs v u∧¬E v u)⊆ordinaryRootResources (X i) (Z i))
    (hcost:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph D E) (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤cost i)
    (hdeepcost:∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph D E (T i) (W i)) (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤deepCost i)
    (havoid:Disjoint (ordinaryPhysicalGraph D E) (ordinaryDeepBlocker (T i) (W i)))
    (hinner:∀target<L,i∈window target→∀v∈I target,
      ordinaryWheelInnerBoundaryError D E (I target) (J target) v≤ inner target i)
    (hcross:∀target<L,i∈window target→∀v∈Parent target,v∉I target→
      ordinaryWheelCrossError D E (I target) (J target) v≤ cross target i):
    OrdinaryUniformProtectedBalanceHistory Q H X T Z W cost deepCost r (i+1) L
      (ordinaryHostResources (G\D) (fun v u=>Hs v u∧¬E v u)) I Parent J window inner cross :=by
  let R:=Function.update h.rim i D
  let S:=Function.update h.spokes i E
  have ht:=ordinary_decomposed_protected_trace_witness_advance Q H X T Z W cost deepCost r i A G D Hs E
    h.rim h.spokes h.trace hstate hD hE hdec hroot hcost hdeepcost havoid
  refine ⟨R,S,ht,?_,?_⟩
  · intro target htarget j hj hjwin v hv
    by_cases hji:j=i
    · subst j
      simpa only [R,S,Function.update_self] using hinner target htarget hjwin v hv
    · have hj':j < i:=by omega
      have hh:=h.inner_boundary target htarget j hj' hjwin v hv
      simpa only [R,S,Function.update_of_ne hji] using hh
  · intro target htarget j hj hjwin v hv hvout
    by_cases hji:j=i
    · subst j
      simpa only [R,S,Function.update_self] using hcross target htarget hjwin v hv hvout
    · have hj':j < i:=by omega
      have hh:=h.cross_boundary target htarget j hj' hjwin v hv hvout
      simpa only [R,S,Function.update_of_ne hji] using hh
end Oberwolfach
