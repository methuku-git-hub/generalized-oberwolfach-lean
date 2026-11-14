module

public import Oberwolfach.OrdinaryTriangleSelectedFactors
public import Oberwolfach.OrdinaryRootTerminalGeometry
public import Oberwolfach.OrdinaryWheelRemainders

@[expose] public section
/-! A boundary decomposition leaves a balanced, divisible remainder supported
on the inner pair, with the actual inner resource cost retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_decomposition_remainder_level
    (Q R:SimpleGraph V) (H S:V→U→Prop) (r:ℕ) (X:Finset V) (Z:Finset U) (limit:ℝ)
    (hRQ:R≤Q) (hSH:∀v u,S v u→H v u) (hdec:HasOrdinaryWheelDecomposition R S r)
    (hQbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hQdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hRsupport:(Q\R).support⊆(X:Set V))
    (hSsupport:∀v u,H v u∧¬S v u→v∈X∧u∈Z)
    (hcost:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit):
    let Q':=Q\R;
    let H':=fun v u=>H v u∧¬S v u;
    Q'≤spanningRestriction Q X ∧ (∀v u,H' v u→H v u∧v∈X∧u∈Z) ∧
    (∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) ∧
    ordinaryHostResources Q' H'⊆ordinaryRootResources X Z ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit):=by
  intro Q' H'
  have hbalance:=ordinary_decomposition_remainder_balance Q R H S r hRQ hSH hQbal hQdiv hdec
  have hsub:Q'≤spanningRestriction Q X:=by
    intro v w hvw
    apply (spanningRestriction_adj Q X v w).mpr
    exact ⟨hvw.1,hRsupport hvw.mem_support_left,hRsupport hvw.mem_support_right⟩
  have hsubH:∀v u,H' v u→H v u∧v∈X∧u∈Z:=by
    intro v u h
    exact ⟨h.1,hSsupport v u h⟩
  refine ⟨hsub,hsubH,?_,?_,?_,hcost⟩
  · intro v;convert hbalance.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro u;convert hbalance.2 u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro e he
    cases e with
    | inl e=>
      induction e using Sym2.ind with
      | _ v w=>
        have hQ:Q'.Adj v w:=(ordinaryHostResources_rim Q' H' s(v,w)).mp he
        have hX:=(spanningRestriction_adj Q X v w).mp (hsub hQ)
        exact ordinaryRootResources_rim X Z v w hX.2.1 hX.2.2
    | inr vu=>
      obtain ⟨v,u⟩:=vu
      have hH:H' v u:=(ordinaryHostResources_spoke Q' H' v u).mp he
      have hX:=hsubH v u hH
      exact ordinaryRootResources_spoke X Z v u hX.2.1 hX.2.2
end Oberwolfach
