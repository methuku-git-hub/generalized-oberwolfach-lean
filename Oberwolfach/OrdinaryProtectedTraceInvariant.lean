module

public import Oberwolfach.OrdinaryProtectedDeletionAppend
public import Oberwolfach.OrdinaryProtectedCoverDownLevelChain

@[expose] public section
/-! A concrete chain invariant recording every selected deletion, its two
costs and its avoidance of the deeper blocker. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryProtectedTrace (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ)
    (n:ℕ) (A:Finset (Sym2 V⊕(V×U))):Prop:=
  ∃(R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop),
    ordinaryHostResources (ordinaryHistoryRim Q R S n) (ordinaryHistorySpokes H R S n)=A ∧
    (n=0 ∨ A⊆ordinaryRootResources (X (n-1)) (Z (n-1))) ∧
    ∀i<n,
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (R i) (S i))
        (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤cost i) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph (R i) (S i) (T i) (W i))
        (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤deepCost i) ∧
      Disjoint (ordinaryPhysicalGraph (R i) (S i)) (ordinaryDeepBlocker (T i) (W i))

theorem ordinary_protected_trace_initial (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ):
    OrdinaryProtectedTrace Q H X T Z W cost deepCost 0 (ordinaryHostResources Q H):=by
  refine ⟨fun _=>⊥,fun _ _ _=>False,?_,Or.inl rfl,?_⟩
  · have hq:ordinaryHistoryRim Q (fun _=>⊥) (fun (_:ℕ) (_:V) (_:U)=>False) 0=Q:=by
      ext a b
      simp [ordinaryHistoryRim,ordinaryDeletionHistory]
    have hh:ordinaryHistorySpokes H (fun _=>⊥) (fun _ _ _=>False) 0=H:=by
      funext v u
      simp [ordinaryHistorySpokes,ordinarySpokesAfterPhysicalDeletion,ordinaryDeletionHistory]
    rw [hq,hh]
  · intro i hi
    omega

theorem ordinary_protected_trace_advance (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ)
    (i:ℕ) (A:Finset (Sym2 V⊕(V×U))) (G D:SimpleGraph V) (Hs E:V→U→Prop)
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost i A)
    (hstate:ordinaryHostResources G Hs=A)
    (hroot:ordinaryHostResources (G\D) (fun v u=>Hs v u∧¬E v u)⊆ordinaryRootResources (X i) (Z i))
    (hcost:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph D E) (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤cost i)
    (hdeepcost:∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph D E (T i) (W i)) (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤deepCost i)
    (havoid:Disjoint (ordinaryPhysicalGraph D E) (ordinaryDeepBlocker (T i) (W i))):
    OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1)
      (ordinaryHostResources (G\D) (fun v u=>Hs v u∧¬E v u)):=by
  obtain ⟨R,S,hist,_,hlevels⟩:=htrace
  obtain ⟨hG,hH⟩:=ordinaryHostResources_injective G (ordinaryHistoryRim Q R S i) Hs
    (ordinaryHistorySpokes H R S i) (hstate.trans hist.symm)
  refine ⟨Function.update R i D,Function.update S i E,?_,Or.inr ?_,?_⟩
  · rw [ordinary_history_append_rim,ordinary_history_append_spokes,←hG,←hH]
  · simpa using hroot
  · intro j hj
    by_cases hji:j=i
    · subst j
      have hR:Function.update R i D i=D:=by simp
      have hS:Function.update S i E i=E:=by simp
      rw [hR,hS]
      convert And.intro hcost (And.intro hdeepcost havoid) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    · have hj' : j < i := by omega
      have hh:=hlevels j hj'
      have hR:Function.update R i D j=R j:=Function.update_of_ne hji _ _
      have hS:Function.update S i E j=S j:=Function.update_of_ne hji _ _
      rw [hR,hS]
      convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _

theorem ordinary_protected_trace_terminal (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ)
    (L:ℕ) (hL:0<L) (A:Finset (Sym2 V⊕(V×U)))
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost L A):
    A⊆ordinaryRootResources (X (L-1)) (Z (L-1)):=by
  obtain ⟨_,_,_,hroot,_⟩:=htrace
  rcases hroot with hzero|hroot
  · omega
  · exact hroot
end Oberwolfach
