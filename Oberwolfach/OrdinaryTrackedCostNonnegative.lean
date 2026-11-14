module

public import Oberwolfach.OrdinaryTrackedComplementCostBudget

@[expose] public section
/-! The explicit discrepancy assigned to the tracked complement is
nonnegative for the naturally nonnegative matching and sampling rates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_cost_nonnegative
    (d n:ℕ) (δ κrate unused delRate σ edit rows hubs:ℝ)
    (hδ:0≤δ) (hκ:0≤κrate) (hunused:0≤unused) (hdel:0≤delRate)
    (hσ:0≤σ) (hedit:0≤edit) (hrows:0≤rows) (hhubs:0≤hubs):
    let LF:ℝ:=2*((3*d:ℕ):ℝ)
    let newLoss:ℝ:=5*Real.sqrt δ*n
    let κref:ℝ:=κrate*n+unused*n+3*(n:ℝ)^(3/5:ℝ)+((6*d+4:ℕ):ℝ)+delRate*n+LF
    let e:ℝ:=σ*n+2*(σ*n)+LF
    let Lrim:ℝ:=edit+κref+newLoss
    let Lspoke:ℝ:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+σ*n);
    0≤Lrim+Lspoke+rows+hubs :=by
  intro LF newLoss κref e Lrim Lspoke
  have hLF:0≤LF:=by dsimp [LF];positivity
  have hnew:0≤newLoss:=by dsimp [newLoss];positivity
  have hk:0≤κref:=by dsimp [κref];positivity
  have he:0≤e:=by dsimp [e];positivity
  have hr:0≤Lrim:=by dsimp [Lrim];positivity
  have hs:0≤Lspoke:=by dsimp [Lspoke];positivity
  positivity
end Oberwolfach
