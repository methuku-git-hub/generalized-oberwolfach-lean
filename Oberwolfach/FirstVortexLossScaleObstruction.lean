module

public import Oberwolfach.MarkedVortexInitialBalanceParentJointLocal
public import Oberwolfach.FirstVortexMatchingScalePositive

@[expose] public section
/-! Diagnostic for using the coarse global degree bound inside a local
correction budget. It does not assert failure of the original theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_loss_scale_obstruction
    (n ε δsmall κ δLoss Δ eta tLocal cLocal rho:ℝ)
    (hn:0<n) (hε:0<ε) (hδ:0<δsmall) (hκ:0≤κ) (hΔ:0≤Δ)
    (hrho:0<rho) (hεsmall:ε<δsmall/2)
    (hdegree:2*(δsmall*n+(κ*n+1))≤δLoss*n)
    (hbudget:Δ+δLoss<eta) (hetat:eta≤tLocal)
    (hlocal:(17+4/rho)*tLocal≤cLocal*ε/2):
    136<cLocal :=by
  have hprod:0≤κ*n:=mul_nonneg hκ hn.le
  have hdl:2*δsmall<δLoss:=by nlinarith
  have heta:2*δsmall<eta:=by linarith
  have ht:0<tLocal:=by linarith
  have hterm:0≤(4/rho)*tLocal:=by positivity
  have hcε:68*δsmall<cLocal*ε:=by nlinarith
  have hcs:0≤cLocal:=by nlinarith
  nlinarith [mul_nonneg hcs (show 0≤δsmall/2-ε by linarith)]
theorem first_vortex_chosen_local_loss_scale_obstruction
    (r:ℕ) (x etaBal n ε δsmall κ δLoss Δ eta tLocal cLocal rho:ℝ)
    (hx:0<x) (hx1:x≤1) (hηBal:0<etaBal)
    (hLocalEq:cLocal=Classical.choose (marked_vortex_initial_balance_from_parent_joint_local_changes r x hx etaBal hηBal))
    (hn:0<n) (hε:0<ε) (hδ:0<δsmall) (hκ:0≤κ) (hΔ:0≤Δ)
    (hrho:0<rho) (hεsmall:ε<δsmall/2)
    (hdegree:2*(δsmall*n+(κ*n+1))≤δLoss*n)
    (hbudget:Δ+δLoss<eta) (hetat:eta≤tLocal)
    (hlocal:(17+4/rho)*tLocal≤cLocal*ε/2):False:=by
  have hlarge:=first_vortex_loss_scale_obstruction n ε δsmall κ δLoss Δ eta tLocal cLocal rho
    hn hε hδ hκ hΔ hrho hεsmall hdegree hbudget hetat hlocal
  have hc0:0<cLocal:=by rw [hLocalEq];exact (Classical.choose_spec (marked_vortex_initial_balance_from_parent_joint_local_changes r x hx etaBal hηBal)).1
  have hcsmall:2*((r+12:ℕ):ℝ)*cLocal≤x/4:=by
    rw [hLocalEq];exact (Classical.choose_spec (marked_vortex_initial_balance_from_parent_joint_local_changes r x hx etaBal hηBal)).2.1
  have hr:(0:ℝ)≤r:=Nat.cast_nonneg _
  push_cast at hcsmall
  nlinarith [mul_nonneg hr hc0.le]
theorem first_vortex_actual_caller_loss_scale_obstruction
    {n D m:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (r:ℕ) (x etaBal εInner δsmall κ δLoss Δ eta tLocal cLocal rho:ℝ)
    (hx:0<x) (hx1:x≤1) (hηBal:0<etaBal)
    (hLocalEq:cLocal=Classical.choose (marked_vortex_initial_balance_from_parent_joint_local_changes r x hx etaBal hηBal))
    (hn:0<n) (hε:0<ε) (hm:0<m) (hδ:0<δsmall) (hκ:0≤κ) (hΔ:0≤Δ) (hrho:0<rho)
    (hinner:((Q.extendedVertices 1).card:ℝ)≤εInner*n) (hgap:εInner<δsmall/4)
    (hdegree:2*(δsmall*n+(κ*n+1))≤δLoss*n)
    (hbudget:Δ+δLoss<eta) (hetat:eta≤tLocal)
    (hlocal:(17+4/rho)*tLocal≤cLocal*ε/2):False:=by
  have hsize:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hsize':ε*(n:ℝ)/2≤((Q.extendedVertices 1).card:ℝ):=by simpa only [Fintype.card_fin] using hsize
  have hsmall:ε<δsmall/2:=by nlinarith
  exact first_vortex_chosen_local_loss_scale_obstruction r x etaBal n ε δsmall κ δLoss Δ eta tLocal cLocal rho
    hx hx1 hηBal hLocalEq hnR hε hδ hκ hΔ hrho hsmall hdegree hbudget hetat hlocal
end Oberwolfach
