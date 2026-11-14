module

public import Oberwolfach.OrdinaryAdaptiveBoundaryReserve

@[expose] public section
/-! A later boundary reserve and any other conditionally likely event are
realized on the same physical-edge sample after the earlier outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_boundary_reserve_with_extra_event (q:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),
      1-e₀≤μ.probability E →
      ∀(Q:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (I:Ω→Finset V) (J:Ω→Finset U)
      (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
      let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1);
      ∀(Extra:Ω→(Sym2 (V⊕U)→Bool)→Prop) (δ:ℝ),0≤δ→
      (∀ω,E ω→1-δ≤ν.probability (Extra ω))→
      1-(e₀+1/(Fintype.card (V⊕U):ℝ)^q+δ)≤
        (μ.sigma (fun _=>ν)).probability (fun z=>E z.1 ∧
          OrdinaryBoundaryReserveGood (Q z.1) (H z.1) (I z.1) (J z.1) τ ε z.2 ∧ Extra z.1 z.2):=by
  obtain ⟨N,hN⟩:=ordinary_boundary_reserve_joint_high_probability q ε hε
  refine ⟨max 1 N,?_⟩
  intro V U Ω _ _ _ _ _ hn μ E e₀ hE Q H I J τ hτ hτ1 ν Extra δ hδ hExtra
  let δ₁:ℝ:=1/(Fintype.card (V⊕U):ℝ)^q
  have hδ₁:0≤δ₁:=by dsimp [δ₁];positivity
  have hP:μ.probability E≤1:=finiteLaw_probability_le_one' μ E
  have hc:∀ω,E ω→1-(δ₁+δ)≤ν.probability
      (fun σ=>OrdinaryBoundaryReserveGood (Q ω) (H ω) (I ω) (J ω) τ ε σ ∧ Extra ω σ):=by
    intro ω hω
    have ha:=hN V U (by omega) (Q ω) (H ω) (I ω) (J ω) τ hτ hτ1
    have hb:=hExtra ω hω
    have hi:=finiteLaw_good_intersection ν (OrdinaryBoundaryReserveGood (Q ω) (H ω) (I ω) (J ω) τ ε) (Extra ω) δ hb
    change 1-δ₁≤_ at ha
    linarith
  have ht:=finiteLaw_twoStage_survival μ (fun _=>ν) E
    (fun ω σ=>OrdinaryBoundaryReserveGood (Q ω) (H ω) (I ω) (J ω) τ ε σ ∧ Extra ω σ) (δ₁+δ) hc
  have hm:(δ₁+δ)*μ.probability E≤δ₁+δ:=by nlinarith only [hδ₁,hδ,hP]
  change 1-(e₀+δ₁+δ)≤_
  nlinarith only [ht,hm,hE]
end Oberwolfach
