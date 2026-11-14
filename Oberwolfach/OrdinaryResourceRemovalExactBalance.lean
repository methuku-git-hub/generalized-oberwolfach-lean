module

public import Oberwolfach.OrdinaryTerminalRemainderBalance

@[expose] public section
/-! Removing a decomposable reserved absorber from the corrected host
preserves exact balance and divisibility for the canonical remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_resource_removal_exact_balance
    (Q P F:SimpleGraph V) (H Hbase:V→U→Prop) (r:ℕ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (K:Finset (Sym2 V⊕(V×U))) (hK:K⊆ordinaryHostResources Q H)
    (hdec:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) K):
    (∀v,(Q\ordinaryResourceRim Q K).degree v=2*(Finset.univ.filter (fun u=>H v u∧¬(Sum.inr (v,u)∈K))).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>H v u∧¬(Sum.inr (v,u)∈K))).card):=by
  let R:=ordinaryResourceRim Q K
  let S:=fun v u=>Sum.inr (v,u)∈K
  obtain ⟨hRQ,hSH,hR⟩:=ordinary_resource_subgraph Q H K hK
  have hd:HasOrdinaryWheelDecomposition R S r:=by
    apply ordinary_host_decomposition_forget (ordinaryHostResources R S)
    rw [hR]
    exact hdec
  have hh:=ordinary_decomposition_remainder_balance Q R H S r hRQ hSH hbal hdiv hd
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
