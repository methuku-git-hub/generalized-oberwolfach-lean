module

public import Oberwolfach.FirstVortexPreparedLocalForTransferBothBudgets
public import Oberwolfach.MarkedVortexActiveTransferFixedMargin
public import Oberwolfach.MarkedExplicitJointBalanceBoundaryBudget

@[expose] public section
/-! Instantiate the ordered caller at the precise level balance and active
transfer caps, preserving their proof-dependent choices. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexExplicitPreparedTransferBothBudgets
    (r k₀:ℕ) (αRef ρ₀ ζFixed levelEta etaBal x:ℝ)
    (hα:0<αRef) (hρ:0<ρ₀) (hζ:0<ζFixed) (hη:0<levelEta)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch:ℝ):Prop :=
    let tstar:ℝ:=1/(200*((r+4:ℕ):ℝ))
    let pstar:ℝ:=ρ₀/(800*((r+4:ℕ):ℝ))
    let BAParent:=successorWeightUpper k₀ ((2*αRef)/4)
    let localCap:=markedExplicitJointLocalCap (r+4) (r+12) etaBal x
    let transferCap:=Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r (2*αRef) tstar pstar ζFixed levelEta BAParent pstar
      hζ hη (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le (by dsimp [pstar]; positivity) (by dsimp [tstar]; positivity));
    let cGlobal:=min cap (1:ℝ)
    let chosenLocal:=min localCap (4*transferCap)
    let c:=min chosenLocal cGlobal
    let active:=c/4
    let θcap:=min (1:ℝ) (min θmax (min (δold/32) (min (δglobal/10) (1/100:ℝ))))
    let κCap:=min (Real.sqrt δglobal/2) (cGlobal/512)
    let lamCap:=min globalRate (3*min ζmax Δmax);
    0<chosenLocal ∧ chosenLocal≤localCap ∧ 0<c ∧ 0<active ∧
      active≤localCap ∧ active≤transferCap ∧ active≤cGlobal/2 ∧
      0<θcap ∧ θcap≤1 ∧ θcap≤θmax ∧ 10*θcap≤δold ∧ θcap≤δold/32 ∧
      10*θcap≤δglobal ∧ θcap≤1/100 ∧ 0<κCap ∧ 0<lamCap ∧
    FirstVortexCallerParametersPrepared r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c c (min eta globalRate) active θcap 1 δold δlocal lamCap κCap bmatch ∧
    FirstVortexCallerParametersPrepared r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c localCap (min eta globalRate) active θcap 1 δold δlocal lamCap κCap bmatch

theorem first_vortex_explicit_prepared_transfer_both_budgets
    (r k₀:ℕ) (αRef ρ₀ ζFixed levelEta etaBal x:ℝ)
    (hα:0<αRef) (hρ:0<ρ₀) (hζ:0<ζFixed) (hη:0<levelEta) (hηBal:0<etaBal) (hx:0<x)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch:ℝ)
    (h:FirstVortexCallerLocalLateCaps r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch):
    FirstVortexExplicitPreparedTransferBothBudgets r k₀ αRef ρ₀ ζFixed levelEta etaBal x hα hρ hζ hη
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch :=by
  dsimp only [FirstVortexExplicitPreparedTransferBothBudgets]
  apply first_vortex_prepared_local_for_transfer_both_budgets r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch _ _ ?_ ?_ h
  · exact (marked_explicit_joint_balance_boundary_budget (r+4) (r+12) etaBal x hηBal hx).1
  · exact (Classical.choose_spec (marked_vortex_active_transfer_from_parent_fixed_margin r (2*αRef)
      (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) ζFixed levelEta
      (successorWeightUpper k₀ ((2*αRef)/4)) (ρ₀/(800*((r+4:ℕ):ℝ))) hζ hη
      (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le (by positivity) (by positivity))).1
end Oberwolfach
