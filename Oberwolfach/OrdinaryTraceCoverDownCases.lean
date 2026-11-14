module

public import Oberwolfach.OrdinaryTraceInducedCoverDown

@[expose] public section
/-! The first ambient level and all subsequent induced levels together
supply the protected cover-down hypothesis for the concrete trace chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_trace_zero_resources
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (A:Finset (Sym2 V⊕(V×U)))
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost 0 A):
    A=ordinaryHostResources Q H:=by
  obtain ⟨R,S,hist,_,_⟩:=htrace
  have hq:ordinaryHistoryRim Q R S 0=Q:=by ext a b;simp [ordinaryHistoryRim,ordinaryDeletionHistory]
  have hh:ordinaryHistorySpokes H R S 0=H:=by
    funext v u
    simp [ordinaryHistorySpokes,ordinarySpokesAfterPhysicalDeletion,ordinaryDeletionHistory]
  rw [hq,hh] at hist
  exact hist.symm

theorem ordinary_protected_trace_coverdown_cases
    (Q F:SimpleGraph V) (H:V→U→Prop) (r L:ℕ)
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ)
    (hfirst:OrdinaryProtectedHostCoverDownResult Q F H (X 0) (T 0) (Z 0) (W 0) r (cost 0) (deepCost 0))
    (hXX:∀i,X (i+1)⊆X i) (hTX:∀i,T (i+1)⊆X i)
    (hZZ:∀i,Z (i+1)⊆Z i) (hWZ:∀i,W (i+1)⊆Z i)
    (hc0:∀i,0≤cost i) (hd0:∀i,0≤deepCost i)
    (hlocal:∀i,i+1<L→∀A (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1) A→
      ordinaryHostResources G Hs=A→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      OrdinaryProtectedHostCoverDownResult (G.induce ((X i):Set V)) (F.induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>Hs v.val u.val)
        (ordinaryContainedTarget (X i) (X (i+1))) (ordinaryContainedTarget (X i) (T (i+1)))
        (ordinaryContainedTarget (Z i) (Z (i+1))) (ordinaryContainedTarget (Z i) (W (i+1))) r
        (cost (i+1)) (deepCost (i+1))):
    ∀i<L,∀A (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryProtectedTrace Q H X T Z W cost deepCost i A→ ordinaryHostResources G Hs=A→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      OrdinaryProtectedHostCoverDownResult G F Hs (X i) (T i) (Z i) (W i) r (cost i) (deepCost i):=by
  intro i hi A G Hs htrace hstate hbal hdiv
  cases i with
  | zero=>
    have he:=ordinary_protected_trace_zero_resources Q H X T Z W cost deepCost A htrace
    obtain ⟨hG,hH⟩:=ordinaryHostResources_injective G Q Hs H (hstate.trans he)
    subst G
    subst Hs
    exact hfirst
  | succ i=>
    have hl:=hlocal i hi A G Hs htrace hstate hbal hdiv
    exact ordinary_trace_induced_coverdown Q H X T Z W cost deepCost i r A G F Hs htrace hstate hbal hdiv
      (hXX i) (hTX i) (hZZ i) (hWZ i) (hc0 (i+1)) (hd0 (i+1)) hl
end Oberwolfach
