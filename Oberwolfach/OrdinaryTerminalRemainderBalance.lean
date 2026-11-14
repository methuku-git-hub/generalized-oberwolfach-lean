module

public import Oberwolfach.OrdinaryResourceSubgraphs
public import Oberwolfach.OrdinaryWheelRemainders
public import Oberwolfach.OrdinaryHostDecompositions

@[expose] public section
/-! Removing any contained wheel-decomposable resource set preserves the
actual remainder's row balance and divisibility at every hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_resource_terminal_remainder_balance
    (Q P F:SimpleGraph V) (H Hbase:V→U→Prop) (r:ℕ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (K:Finset (Sym2 V⊕(V×U))) (hK:K⊆ordinaryHostResources Q H)
    (hdec:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) K):
    ∃(Gterm:SimpleGraph V) (Hterm:V→U→Prop),
      ordinaryHostResources Gterm Hterm=ordinaryHostResources Q H\K ∧
      (∀v,Gterm.degree v=2*(Finset.univ.filter (Hterm v)).card) ∧
      (∀u,r∣(Finset.univ.filter (fun v=>Hterm v u)).card) ∧
      Gterm≤Q ∧ (∀v u,Hterm v u→H v u):=by
  let R:=ordinaryResourceRim Q K
  let S:=fun v u=>Sum.inr (v,u)∈K
  obtain ⟨hRQ,hSH,hR⟩:=ordinary_resource_subgraph Q H K hK
  have hd:HasOrdinaryWheelDecomposition R S r:=by
    apply ordinary_host_decomposition_forget (ordinaryHostResources R S)
    rw [hR]
    exact hdec
  obtain ⟨hb,hu⟩:=ordinary_decomposition_remainder_balance Q R H S r hRQ hSH hbal hdiv hd
  refine ⟨Q\R,fun v u=>H v u∧¬S v u,?_,?_,?_,?_,?_⟩
  · rw [ordinaryHostResources_sdiff,hR]
  · intro v
    have hh:=hb v
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  · intro u
    have hh:=hu u
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  · intro v w h
    exact h.1
  · intro v u h
    exact h.1
end Oberwolfach
