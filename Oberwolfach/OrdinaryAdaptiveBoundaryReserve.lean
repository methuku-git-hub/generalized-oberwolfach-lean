module

public import Oberwolfach.OrdinaryBoundaryReserveJointEvent
public import Oberwolfach.TwoStageEvents
public import Oberwolfach.ProductFailureBounds

@[expose] public section
/-! The boundary reserve is sampled after an arbitrary earlier outcome and
its host has been chosen; the original outcome and its event are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_boundary_reserve_high_probability (q:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀:ℝ),
      1-e₀≤μ.probability E →
      ∀(Q:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (I:Ω→Finset V) (J:Ω→Finset U)
      (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
      let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1);
      1-(e₀+1/(Fintype.card (V⊕U):ℝ)^q)≤
        (μ.sigma (fun _=>ν)).probability (fun z=>E z.1 ∧ OrdinaryBoundaryReserveGood (Q z.1) (H z.1) (I z.1) (J z.1) τ ε z.2):=by
  obtain ⟨N,hN⟩:=ordinary_boundary_reserve_joint_high_probability q ε hε
  refine ⟨max 1 N,?_⟩
  intro V U Ω _ _ _ _ _ hn μ E e₀ hE Q H I J τ hτ hτ1 ν
  let δ:ℝ:=1/(Fintype.card (V⊕U):ℝ)^q
  have hδ:0≤δ:=by dsimp [δ];positivity
  have hP:μ.probability E≤1:=finiteLaw_probability_le_one' μ E
  have hconditional:∀ω,E ω→1-δ≤ν.probability (OrdinaryBoundaryReserveGood (Q ω) (H ω) (I ω) (J ω) τ ε):=by
    intro ω _
    exact hN V U (by omega) (Q ω) (H ω) (I ω) (J ω) τ hτ hτ1
  have ht:=finiteLaw_twoStage_survival μ (fun _=>ν) E
    (fun ω σ=>OrdinaryBoundaryReserveGood (Q ω) (H ω) (I ω) (J ω) τ ε σ) δ hconditional
  have hm:δ*μ.probability E≤δ:=by nlinarith only [hδ,hP]
  change 1-(e₀+δ)≤_
  nlinarith only [ht,hm,hE]
end Oberwolfach
