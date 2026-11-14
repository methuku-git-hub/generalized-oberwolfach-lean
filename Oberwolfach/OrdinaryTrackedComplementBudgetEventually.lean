module

public import Oberwolfach.OrdinaryTrackedComplementFiniteErrors
public import Oberwolfach.OrdinaryTrackedComplementCostBudget

@[expose] public section
/-! Once the hierarchy has selected the small rates and fixed absorber size,
the actual remainder's explicit error is eventually a small linear bound. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem ordinary_tracked_complement_budget_eventually
    (d tAbs aAbs bAbs:ℕ) (η δ θ κrate delRate σ:ℝ)
    (hη:0<η) (hδ:0≤δ) (hδ1:δ≤1) (hcap:5*Real.sqrt δ≤η)
    (hθ:θ≤δ/8) (hκ:κrate≤δ) (hdel:delRate≤δ) (hσ:σ≤η):
    ∃N:ℕ,∀n:ℕ,N≤n→∀unused edit rows hubs:ℝ,
    unused≤2*θ→edit≤η*n→
    rows+hubs≤((2^(tAbs*tAbs)*aAbs+2^(tAbs*tAbs)*bAbs:ℕ):ℝ)→
    let LF:ℝ:=2*((3*d:ℕ):ℝ)
    let newLoss:ℝ:=5*Real.sqrt δ*n
    let κref:ℝ:=κrate*n+unused*n+3*(n:ℝ)^(3/5:ℝ)+((6*d+4:ℕ):ℝ)+delRate*n+LF
    let e:ℝ:=σ*n+2*(σ*n)+LF
    let Lrim:ℝ:=edit+κref+newLoss
    let Lspoke:ℝ:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+σ*n);
    Lrim+Lspoke+rows+hubs≤14*η*n :=by
  let LF:ℝ:=2*((3*d:ℕ):ℝ)
  let C:ℝ:=((6*d+4:ℕ):ℝ)+LF+((2^(tAbs*tAbs)*aAbs+2^(tAbs*tAbs)*bAbs:ℕ):ℝ)
  have hC:0≤C:=by dsimp [C,LF];positivity
  obtain ⟨N,hN⟩:=ordinary_tracked_complement_finite_errors C η hC hη
  refine ⟨N,?_⟩
  intro n hn unused edit rows hubs hUnused hEdit hRows LF' newLoss κref e Lrim Lspoke
  have hn0:(0:ℝ)≤n:=by positivity
  have hpow:0≤(n:ℝ)^(3/5:ℝ):=by positivity
  have hLF:0≤LF:=by dsimp [LF];positivity
  have hconst:0≤((2^(tAbs*tAbs)*aAbs+2^(tAbs*tAbs)*bAbs:ℕ):ℝ):=by positivity
  have hfinite:=hN n hn
  have hrest:3*(n:ℝ)^(3/5:ℝ)+((6*d+4:ℕ):ℝ)+LF≤η*n:=by dsimp [C] at hfinite;linarith
  have hLFsmall:LF≤η*n:=by dsimp [C] at hfinite;linarith
  have hressmall:rows+hubs≤η*n:=by dsimp [C] at hfinite;linarith
  have hσn:σ*n≤η*n:=mul_le_mul_of_nonneg_right hσ hn0
  have he:e≤4*η*n:=by dsimp [e,LF'];linarith
  have hδeta:=ordinary_sqrt_cap_controls_residual_rate δ η hδ hδ1 hcap
  have hnew:5*Real.sqrt δ*n≤η*n:=mul_le_mul_of_nonneg_right hcap hn0
  have hκn:κrate*n≤δ*n:=mul_le_mul_of_nonneg_right hκ hn0
  have hdln:delRate*n≤δ*n:=mul_le_mul_of_nonneg_right hdel hn0
  have hh:=ordinary_tracked_complement_cost_budget n η δ θ unused (κrate*n) edit
    (3*(n:ℝ)^(3/5:ℝ)+((6*d+4:ℕ):ℝ)+LF) (delRate*n) e (σ*n) (rows+hubs)
    hn0 hη.le hδ hδeta hθ hUnused hκn hEdit hrest hdln hnew he hσn hressmall
  dsimp only [newLoss,κref,e,Lrim,Lspoke,LF'] at *
  dsimp only [LF] at hh
  ring_nf at hh ⊢
  exact hh
end Oberwolfach
