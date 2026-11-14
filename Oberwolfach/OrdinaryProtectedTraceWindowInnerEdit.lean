module

public import Oberwolfach.OrdinaryProtectedTraceInvariant
public import Oberwolfach.OrdinaryDeletionHistoryWindowEdit

@[expose] public section
/-! In a protected trace with a longer buffer, only a finite window of
    recent cover-downs can edit the current inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_trace_window_inner_edit
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (J:Finset ℕ)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G Hs=A)
    (hJ:∀j∈J,j < i+1)
    (hX:∀j < i+1,j∉J→X i⊆T j) (hZ:∀j < i+1,j∉J→Z i⊆W j)
    (hXnest:∀j∈J,X i⊆X j) (hZnest:∀j∈J,Z i⊆Z j):
    let B:=spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices (X i) (Z i));
    let B':=spanningRestriction (ordinaryPhysicalGraph G Hs) (ordinaryInnerVertices (X i) (Z i));
    ∀w:V⊕U,((changed (B.neighborFinset w) (B'.neighborFinset w)).card:ℝ)≤∑j∈J,cost j :=by
  intro B B'
  obtain ⟨R,S,hist,_,hlevels⟩:=htrace
  obtain ⟨hG,hH⟩:=ordinaryHostResources_injective G (ordinaryHistoryRim Q R S (i+1)) Hs
    (ordinaryHistorySpokes H R S (i+1)) (hstate.trans hist.symm)
  subst G
  subst Hs
  have hzero:∀j < i+1,j∉J→spanningRestriction (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryInnerVertices (X i) (Z i))=⊥:=by
    intro j hj hjnot
    exact ordinary_protected_inner_zero_nested (R j) (S j) (X i) (T j) (Z i) (W j)
      (hX j hj hjnot) (hZ j hj hjnot) (hlevels j hj).2.2
  have hcost:∀j∈J,∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤cost j:=by
    intro j hj w
    have hinner:ordinaryInnerVertices (X i) (Z i)⊆ordinaryInnerVertices (X j) (Z j):=by
      intro v hv
      cases v with
      | inl v => exact (ordinaryInnerVertices_left (X j) (Z j) v).mpr (hXnest j hj ((ordinaryInnerVertices_left (X i) (Z i) v).mp hv))
      | inr u => exact (ordinaryInnerVertices_right (X j) (Z j) u).mpr (hZnest j hj ((ordinaryInnerVertices_right (X i) (Z i) u).mp hv))
    have hsub:spanningRestriction (ordinaryPhysicalGraph (R j) (S j)) (ordinaryInnerVertices (X i) (Z i))≤
        spanningRestriction (ordinaryPhysicalGraph (R j) (S j)) (ordinaryInnerVertices (X j) (Z j)):=by
      intro a b hab
      obtain ⟨he,ha,hb⟩:=(spanningRestriction_adj _ _ _ _).mp hab
      exact (spanningRestriction_adj _ _ _ _).mpr ⟨he,hinner ha,hinner hb⟩
    have hd:=SimpleGraph.degree_le_of_le hsub (v:=w)
    have hdr:((spanningRestriction (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤
      (spanningRestriction (ordinaryPhysicalGraph (R j) (S j)) (ordinaryInnerVertices (X j) (Z j))).degree w:=by exact_mod_cast hd
    exact hdr.trans ((hlevels j (hJ j hj)).1 w)
  have hh:=ordinary_deletion_history_inner_window_edit Q H R S (i+1) (X i) (Z i) J cost hzero hcost
  intro w
  convert hh w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
