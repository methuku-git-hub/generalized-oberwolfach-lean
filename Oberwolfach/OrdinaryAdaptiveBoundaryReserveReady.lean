module

public import Oberwolfach.OrdinaryAdaptiveBoundaryReserve
public import Oberwolfach.OrdinaryBoundaryReserveReady

@[expose] public section
/-! The fresh reserve is chosen after the earlier outcome, and the actual
resulting host and degree estimates are retained on that same outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_boundary_reserve_ready_high_probability (q:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),
      1-e₀≤μ.probability E →
      ∀(Q:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (I:Ω→Finset V) (J:Ω→Finset U)
      (b c:Ω→ℝ),
      (∀ω,E ω→∀v,(Q ω).degree v=2*(Finset.univ.filter (H ω v)).card) →
      (∀ω,E ω→∀v,|((spanningRestriction (Q ω) (I ω)).degree v:ℝ)-
        2*(Finset.univ.filter (fun u=>H ω v u∧v∈I ω∧u∈J ω)).card|≤b ω) →
      (∀ω,E ω→∀v∉I ω,|(((Q ω).neighborFinset v∩I ω).card:ℝ)-2*((J ω).filter (H ω v)).card|≤c ω) →
      ∀(τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
      let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1);
      1-(e₀+1/(Fintype.card (V⊕U):ℝ)^q)≤
        (μ.sigma (fun _=>ν)).probability (fun z=>E z.1 ∧
          let R:=retainedGraph (ordinaryBoundaryGraph (Q z.1) (H z.1) (I z.1) (J z.1)) z.2;
          (R.comap Sum.inl)≤Q z.1\spanningRestriction (Q z.1) (I z.1) ∧
          (∀v u,R.Adj (Sum.inl v) (Sum.inr u)→H z.1 v u∧¬(v∈I z.1∧u∈J z.1)) ∧
          (∀v,((R.comap Sum.inl).degree v:ℝ)≤(τ+ε)*Fintype.card (V⊕U)) ∧
          (∀v,((Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤(τ+ε)*Fintype.card (V⊕U)) ∧
          (∀u,((Finset.univ.filter (fun v=>R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤(τ+ε)*Fintype.card (V⊕U)) ∧
          (∀v,|((((Q z.1\spanningRestriction (Q z.1) (I z.1))\(R.comap Sum.inl)).degree v):ℝ)-
            2*(Finset.univ.filter (fun u=>(H z.1 v u∧¬(v∈I z.1∧u∈J z.1))∧¬R.Adj (Sum.inl v) (Sum.inr u))).card|
              ≤b z.1+τ*max (b z.1) (c z.1)+3*ε*Fintype.card (V⊕U))):=by
  obtain ⟨N,hN⟩:=ordinary_adaptive_boundary_reserve_high_probability q ε hε
  refine ⟨N,?_⟩
  intro V U Ω _ _ _ _ _ hn μ E e₀ hE Q H I J b c hbal hinner hcross τ hτ hτ1 ν
  have h:=hN V U Ω hn μ E e₀ hE Q H I J τ hτ hτ1
  apply h.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  exact ordinary_boundary_reserve_ready (Q z.1) (H z.1) (I z.1) (J z.1) τ ε (b z.1) (c z.1) hτ z.2 hz.2
    (hbal z.1 hz.1) (hinner z.1 hz.1) (hcross z.1 hz.1)
end Oberwolfach
