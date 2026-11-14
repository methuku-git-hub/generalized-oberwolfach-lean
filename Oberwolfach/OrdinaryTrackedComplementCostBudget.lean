module

public import Oberwolfach.OrdinaryTrackedComplementFromMatchingShape

@[expose] public section
/-! Convert the explicit physical-comparison cost to a small linear rate
after all sample, deletion and absorber errors have been chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_tracked_complement_cost_budget
    (n η δ θ unused κ edit errorRest deletion e tcol resources:ℝ)
    (hn:0≤n) (hη:0≤η) (hδ:0≤δ) (hδη:δ≤η)
    (hθ:θ≤δ/8) (hUnused:unused≤2*θ)
    (hκ:κ≤δ*n) (hEdit:edit≤η*n) (hRest:errorRest≤η*n)
    (hDel:deletion≤δ*n) (hNew:5*Real.sqrt δ*n≤η*n)
    (hE:e≤4*η*n) (hCol:tcol≤η*n) (hRes:resources≤η*n):
    let newLoss:=5*Real.sqrt δ*n
    let κref:=κ+unused*n+errorRest+deletion
    let Lrim:=edit+κref+newLoss
    let Lspoke:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+tcol);
    Lrim+Lspoke+resources≤14*η*n :=by
  intro newLoss κref Lrim Lspoke
  have hd:δ*n≤η*n:=mul_le_mul_of_nonneg_right hδη hn
  have hηn:0≤η*n:=mul_nonneg hη hn
  have hu:unused≤η:=by linarith
  have hun:unused*n≤η*n:=mul_le_mul_of_nonneg_right hu hn
  have hkr:κref≤4*η*n:=by dsimp [κref];linarith
  have hr:Lrim≤6*η*n:=by dsimp [Lrim];linarith
  have hs:Lspoke≤7*η*n:=by
    dsimp [Lspoke]
    apply max_le <;> linarith
  linarith

theorem ordinary_sqrt_cap_controls_residual_rate
    (δ η:ℝ) (hδ:0≤δ) (hδ1:δ≤1) (hcap:5*Real.sqrt δ≤η):δ≤η :=by
  have hs:0≤Real.sqrt δ:=Real.sqrt_nonneg δ
  have heq:(Real.sqrt δ)^2=δ:=Real.sq_sqrt hδ
  have hsmall:Real.sqrt δ≤1:=by
    by_contra h
    have hh:1<Real.sqrt δ:=lt_of_not_ge h
    nlinarith
  nlinarith
end Oberwolfach
