module

public import Oberwolfach.OrdinaryBoundaryReserveDegreeBounds
public import Oberwolfach.OrdinaryBoundaryReservedNearBalance
public import Oberwolfach.OrdinaryBoundaryBalanceProfiles

@[expose] public section
/-! The actual sampled boundary reserve supplies bounded degrees and leaves
near balance, under the full, inner and cross profile bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_reserve_ready
    (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U) (τ ε b c:ℝ)
    (hτ:0≤τ) (σ:Sym2 (V⊕U)→Bool) (hgood:OrdinaryBoundaryReserveGood Q H I J τ ε σ)
    (hQbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hinner:∀v,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b)
    (hcross:∀v∉I,|((Q.neighborFinset v∩I).card:ℝ)-2*(J.filter (H v)).card|≤c):
    let R:=retainedGraph (ordinaryBoundaryGraph Q H I J) σ;
    (R.comap Sum.inl)≤Q\spanningRestriction Q I ∧
    (∀v u,R.Adj (Sum.inl v) (Sum.inr u)→H v u∧¬(v∈I∧u∈J)) ∧
    (∀v,((R.comap Sum.inl).degree v:ℝ)≤(τ+ε)*Fintype.card (V⊕U)) ∧
    (∀v,((Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤(τ+ε)*Fintype.card (V⊕U)) ∧
    (∀u,((Finset.univ.filter (fun v=>R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤(τ+ε)*Fintype.card (V⊕U)) ∧
    (∀v,|((((Q\spanningRestriction Q I)\(R.comap Sum.inl)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u=>(H v u∧¬(v∈I∧u∈J))∧¬R.Adj (Sum.inl v) (Sum.inr u))).card|
        ≤b+τ*max b c+3*ε*Fintype.card (V⊕U)):=by
  intro R
  have hfull:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤0:=by
    intro v
    have hv:(Q.degree v:ℝ)=2*(Finset.univ.filter (H v)).card:=by exact_mod_cast hQbal v
    rw [hv,sub_self,abs_zero]
  have hprofile:=ordinary_boundary_balance_from_profiles Q H I J 0 b c hfull hinner hcross
  have hB:let B:=ordinaryBoundaryGraph Q H I J;
      ∀v,|((B.comap Sum.inl).degree v:ℝ)-2*(Finset.univ.filter (fun u=>B.Adj (Sum.inl v) (Sum.inr u))).card|≤max b c:=by
    intro B v
    have hh:=hprofile v
    convert hh using 1 <;> simp <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hRet:let B:=ordinaryBoundaryGraph Q H I J;let R:=retainedGraph B σ;
      ∀v,|(((R.comap Sum.inl).degree v:ℝ)-2*(Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))).card)-
        τ*((B.comap Sum.inl).degree v-2*(Finset.univ.filter (fun u=>B.Adj (Sum.inl v) (Sum.inr u))).card)|
        ≤3*ε*Fintype.card (V⊕U):=by
    intro B R v
    exact (hgood.2 v).le
  have hn:=ordinary_boundary_reserved_near_balance Q H I J σ τ b (max b c) (3*ε*Fintype.card (V⊕U))
    hτ hQbal hinner hB hRet
  have hg:=ordinary_boundary_reserve_geometry Q H I J σ
  have hd:=ordinary_boundary_reserve_degree_bounds Q H I J τ ε hτ σ hgood
  exact ⟨hg.1,hg.2,hd.1,hd.2.1,hd.2.2,hn⟩
end Oberwolfach
