module

public import Oberwolfach.OrdinaryBoundaryReserveReady
public import Oberwolfach.OrdinaryUnreservedPackingCertificate

@[expose] public section
/-! The sampled reserve and the original inner/cross profiles discharge the
near-balance hypothesis for the actual unreserved packing host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_balance_from_reserve
    (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (τ ε b c η:ℝ) (hτ:0≤τ) (σ:Sym2 (V⊕U)→Bool)
    (hgood:OrdinaryBoundaryReserveGood Q H X Z τ ε σ)
    (hQbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤b)
    (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤c)
    (hbudget:b+τ*max b c+3*ε*Fintype.card (V⊕U)≤η*Fintype.card V):
    let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ;
    ∀v,|((ordinaryUnreservedRim Q X R).degree v:ℝ)-
      2*(Finset.univ.filter (ordinaryUnreservedSpokes H X Z R v)).card|≤η*Fintype.card V:=by
  intro R v
  have hh:=(ordinary_boundary_reserve_ready Q H X Z τ ε b c hτ σ hgood hQbal hinner hcross).2.2.2.2.2 v
  have he:(Finset.univ.filter (ordinaryUnreservedSpokes H X Z R v))=
      Finset.univ.filter (fun u=>(H v u∧¬(v∈X∧u∈Z))∧¬R.Adj (Sum.inl v) (Sum.inr u)):=by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,ordinaryUnreservedSpokes]
    tauto
  have hr:ordinaryUnreservedRim Q X R=(Q\spanningRestriction Q X)\R.comap Sum.inl:=rfl
  rw [hr,he]
  convert hh.trans hbudget using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
