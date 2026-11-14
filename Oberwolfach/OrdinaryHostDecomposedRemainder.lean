module

public import Oberwolfach.OrdinaryProfileTransformerCompletion
public import Oberwolfach.OrdinaryWheelRemainders

@[expose] public section
/-! A wheel decomposition witnessed in an actual host is a subhost, so
removing it preserves balance and hub divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_host_decomposed_remainder (Q R F:SimpleGraph V) (H S:V→U→Prop) (r:ℕ)
    (hhost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R S))
    (hdec:HasOrdinaryWheelDecomposition R S r)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    R≤Q ∧ (∀v u,S v u→H v u) ∧
    (∀v,(Q\R).degree v=2*(Finset.univ.filter (fun u=>H v u∧¬S v u)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>H v u∧¬S v u)).card):=by
  have hsub:=ordinary_host_decomposition_subhost (ordinaryHostResources R S) hhost
  have hr:R≤Q:=by
    intro v w hvw
    change s(v,w)∈Q.edgeSet
    apply (ordinaryHostResources_rim Q H _).mp
    apply hsub
    apply (ordinaryHostResources_rim R S _).mpr
    change R.Adj v w
    exact hvw
  have hs:∀v u,S v u→H v u:=by
    intro v u hvu
    apply (ordinaryHostResources_spoke Q H v u).mp
    apply hsub
    exact (ordinaryHostResources_spoke R S v u).mpr hvu
  have hh:=ordinary_decomposition_remainder_balance Q R H S r hr hs hbal hdiv hdec
  exact ⟨hr,hs,hh.1,hh.2⟩
end Oberwolfach
