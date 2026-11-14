module

public import Oberwolfach.OrdinaryProtectedTraceInvariant
public import Oberwolfach.OrdinaryWheelDeletionBoundaryBalanceChain

@[expose] public section
/-! Keep the actual wheel-decomposed deletions in the protected-trace witness,
so later balance arguments can use cancellation across each deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryDecomposedProtectedTrace (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ)
    (r n:ℕ) (A:Finset (Sym2 V⊕(V×U))):Prop:=
  ∃(R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop),
    ordinaryHostResources (ordinaryHistoryRim Q R S n) (ordinaryHistorySpokes H R S n)=A ∧
    (n=0 ∨ A⊆ordinaryRootResources (X (n-1)) (Z (n-1))) ∧
    (∀i<n,
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (R i) (S i))
        (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤cost i) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph (R i) (S i) (T i) (W i))
        (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤deepCost i) ∧
      Disjoint (ordinaryPhysicalGraph (R i) (S i)) (ordinaryDeepBlocker (T i) (W i))) ∧
    ∀i<n,R i≤ordinaryHistoryRim Q R S i ∧
      (∀v u,S i v u→ ordinaryHistorySpokes H R S i v u) ∧ HasOrdinaryWheelDecomposition (R i) (S i) r

theorem ordinary_decomposed_protected_trace_forget
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (r n:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (h:OrdinaryDecomposedProtectedTrace Q H X T Z W cost deepCost r n A):
    OrdinaryProtectedTrace Q H X T Z W cost deepCost n A :=by
  obtain ⟨R,S,hstate,hroot,hlevels,_⟩:=h
  exact ⟨R,S,hstate,hroot,hlevels⟩

theorem ordinary_decomposed_protected_trace_initial
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (r:ℕ):
    OrdinaryDecomposedProtectedTrace Q H X T Z W cost deepCost r 0 (ordinaryHostResources Q H) :=by
  refine ⟨fun _=>⊥,fun _ _ _=>False,?_,Or.inl rfl,?_,?_⟩
  · have hq:ordinaryHistoryRim Q (fun _=>⊥) (fun (_:ℕ) (_:V) (_:U)=>False) 0=Q:=by
      ext a b
      simp [ordinaryHistoryRim,ordinaryDeletionHistory]
    have hh:ordinaryHistorySpokes H (fun _=>⊥) (fun (_:ℕ) (_:V) (_:U)=>False) 0=H:=by
      funext v u
      simp [ordinaryHistorySpokes,ordinarySpokesAfterPhysicalDeletion,ordinaryDeletionHistory]
    rw [hq,hh]
  · intro i hi;omega
  · intro i hi;omega

theorem ordinary_decomposed_protected_trace_advance
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (r i:ℕ) (A:Finset (Sym2 V⊕(V×U))) (G D:SimpleGraph V) (Hs E:V→U→Prop)
    (htrace:OrdinaryDecomposedProtectedTrace Q H X T Z W cost deepCost r i A)
    (hstate:ordinaryHostResources G Hs=A) (hD:D≤G) (hE:∀v u,E v u→Hs v u)
    (hdec:HasOrdinaryWheelDecomposition D E r)
    (hroot:ordinaryHostResources (G\D) (fun v u=>Hs v u∧¬E v u)⊆ordinaryRootResources (X i) (Z i))
    (hcost:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph D E) (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤cost i)
    (hdeepcost:∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph D E (T i) (W i)) (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤deepCost i)
    (havoid:Disjoint (ordinaryPhysicalGraph D E) (ordinaryDeepBlocker (T i) (W i))):
    OrdinaryDecomposedProtectedTrace Q H X T Z W cost deepCost r (i+1)
      (ordinaryHostResources (G\D) (fun v u=>Hs v u∧¬E v u)) :=by
  obtain ⟨R,S,hist,_,hlevels,hdecomp⟩:=htrace
  obtain ⟨hG,hH⟩:=ordinaryHostResources_injective G (ordinaryHistoryRim Q R S i) Hs
    (ordinaryHistorySpokes H R S i) (hstate.trans hist.symm)
  refine ⟨Function.update R i D,Function.update S i E,?_,Or.inr ?_,?_,?_⟩
  · rw [ordinary_history_append_rim,ordinary_history_append_spokes,←hG,←hH]
  · simpa using hroot
  · intro j hj
    by_cases hji:j=i
    · subst j
      have hR:Function.update R i D i=D:=by simp
      have hS:Function.update S i E i=E:=by simp
      rw [hR,hS]
      convert And.intro hcost (And.intro hdeepcost havoid) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    · have hj' : j < i:=by omega
      have hh:=hlevels j hj'
      have hR:Function.update R i D j=R j:=Function.update_of_ne hji _ _
      have hS:Function.update S i E j=S j:=Function.update_of_ne hji _ _
      rw [hR,hS]
      convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro j hj
    have hhist:ordinaryDeletionHistory (Function.update R i D) (Function.update S i E) j=
        ordinaryDeletionHistory R S j:=by
      apply ordinary_deletion_history_congr
      · intro k hk;exact Function.update_of_ne (by omega) _ _
      · intro k hk;exact Function.update_of_ne (by omega) _ _
    have hRq:ordinaryHistoryRim Q (Function.update R i D) (Function.update S i E) j=ordinaryHistoryRim Q R S j:=by
      simp only [ordinaryHistoryRim,hhist]
    have hSh:ordinaryHistorySpokes H (Function.update R i D) (Function.update S i E) j=ordinaryHistorySpokes H R S j:=by
      simp only [ordinaryHistorySpokes,hhist]
    rw [hRq,hSh]
    by_cases hji:j=i
    · subst j
      simp only [Function.update_self]
      exact ⟨by simpa only [←hG] using hD,by simpa only [←hH] using hE,hdec⟩
    · have hj' : j < i:=by omega
      rw [Function.update_of_ne hji,Function.update_of_ne hji]
      exact hdecomp j hj'
end Oberwolfach
