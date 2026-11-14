module

public import Oberwolfach.MarkedExplicitJointBalanceBoundaryBudget
public import Oberwolfach.FirstVortexMatchingScalePositive

@[expose] public section
/-! The actual first vortex has a positive fraction of the host. Consequently
late global load choices also have to dominate that previously fixed ratio. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_explicit_balance_window_requires_vortex_ratio
    {n D m:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (r:ℕ) (etaBal x εInner δsmall etaGlobal rho:ℝ)
    (hn:0<n) (hε:0<ε) (hm:0<m) (hrho:0<rho)
    (hinner:((Q.extendedVertices 1).card:ℝ)≤εInner*n)
    (hgap:εInner*n≤δsmall*n/4)
    (hLoss:2*δsmall<etaGlobal)
    (hEta:etaGlobal≤markedExplicitJointLocalCap (r+4) (r+12) etaBal x*rho/4):
    256*(((r+12:ℕ):ℝ)+1)*ε<rho*x ∧
    256*((r+4+4:ℕ):ℝ)*ε<rho*etaBal :=by
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hsize:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
  have hsize':ε*(n:ℝ)/2≤((Q.extendedVertices 1).card:ℝ):=by simpa only [Fintype.card_fin] using hsize
  have hεδ:2*ε≤δsmall:=by nlinarith
  let c:=markedExplicitJointLocalCap (r+4) (r+12) etaBal x
  have hcX:c≤x/(16*(((r+12:ℕ):ℝ)+1)):=by dsimp [c,markedExplicitJointLocalCap];exact min_le_left _ _
  have hcE:c≤etaBal/(16*((r+4+4:ℕ):ℝ)):=by dsimp [c,markedExplicitJointLocalCap];exact (min_le_right _ _).trans (min_le_right _ _)
  have hX:16*(((r+12:ℕ):ℝ)+1)*c≤x:=by
    have hh:=(le_div_iff₀ (show 0<16*(((r+12:ℕ):ℝ)+1) by positivity)).mp hcX
    nlinarith
  have hE:16*((r+4+4:ℕ):ℝ)*c≤etaBal:=by
    have hh:=(le_div_iff₀ (show 0<16*((r+4+4:ℕ):ℝ) by positivity)).mp hcE
    nlinarith
  have hG:8*δsmall<c*rho:=by dsimp [c] at *;linarith
  have hXX:=mul_le_mul_of_nonneg_right hX hrho.le
  have hEE:=mul_le_mul_of_nonneg_right hE hrho.le
  have hXG:=mul_lt_mul_of_pos_left hG (show 0<16*(((r+12:ℕ):ℝ)+1) by positivity)
  have hEG:=mul_lt_mul_of_pos_left hG (show 0<16*((r+4+4:ℕ):ℝ) by positivity)
  have hh:(0:ℝ)≤((r+12:ℕ):ℝ)+1:=by positivity
  have hk:(0:ℝ)≤((r+4+4:ℕ):ℝ):=by positivity
  constructor <;> nlinarith [mul_nonneg hh (show 0≤δsmall-2*ε by linarith),mul_nonneg hk (show 0≤δsmall-2*ε by linarith)]
end Oberwolfach
