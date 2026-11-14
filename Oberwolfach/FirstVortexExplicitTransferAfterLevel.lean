module

public import Oberwolfach.FirstVortexInitialTransferAfterRates
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

def FirstVortexExplicitTransferAfterLevel
    (r k₀:ℕ) (αRef ρ₀ ζFixed levelEta etaBal x:ℝ)
    (hα:0<αRef) (hρ:0<ρ₀) (hζ:0<ζFixed) (hη:0<levelEta)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε:ℝ):Prop :=
    let tstar:ℝ:=1/(200*((r+4:ℕ):ℝ))
    let pstar:ℝ:=ρ₀/(800*((r+4:ℕ):ℝ))
    let BAParent:=successorWeightUpper k₀ ((2*αRef)/4)
    let localCap:=markedExplicitJointLocalCap (r+4) (r+12) etaBal x
    let transferCap:=Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r (2*αRef) tstar pstar ζFixed levelEta BAParent pstar
      hζ hη (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le (by dsimp [pstar]; positivity) (by dsimp [tstar]; positivity));
    ∀(θUpper assignUpper:ℝ),0<θUpper→0<assignUpper→
    ∃δold δlocal:ℝ,0<δold ∧ δold≤1 ∧ δold<δlocal ∧ δlocal≤δglobal ∧
    let cGlobal:=min cap (1:ℝ)
    let chosenLocal:=min localCap (4*transferCap)
    let c:=min chosenLocal cGlobal
    let active:=c/4
    let θcap:=min θUpper (min θmax (min (δold/32) (min (δglobal/10) (1/100:ℝ))))
    let κCap:=min (Real.sqrt δglobal/2) (cGlobal/512)
    let lamCap:=min globalRate (3*min ζmax Δmax);
    0<chosenLocal ∧ chosenLocal≤localCap ∧ 0<c ∧ 0<active ∧
      active≤localCap ∧ active≤transferCap ∧ active≤cGlobal/2 ∧
      0<θcap ∧ θcap≤θUpper ∧ θcap≤θmax ∧ 10*θcap≤δold ∧ θcap≤δold/32 ∧
      10*θcap≤δglobal ∧ θcap≤1/100 ∧ 0<κCap ∧ 0<lamCap ∧
    FirstVortexPackingWithCallerBudgets r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c chosenLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap

theorem first_vortex_explicit_transfer_after_level
    (r k₀:ℕ) (αRef ρ₀ ζFixed levelEta etaBal x:ℝ)
    (hα:0<αRef) (hρ:0<ρ₀) (hζ:0<ζFixed) (hη:0<levelEta) (hηBal:0<etaBal) (hx:0<x)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε:ℝ)
    (h:FirstVortexInitialTransferAfterRates r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε):
    FirstVortexExplicitTransferAfterLevel r k₀ αRef ρ₀ ζFixed levelEta etaBal x hα hρ hζ hη
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε :=by
  dsimp only [FirstVortexExplicitTransferAfterLevel]
  intro θUpper assignUpper hθUpper hAssign
  apply h _ _ θUpper assignUpper ?_ ?_ hθUpper hAssign
  · exact (marked_explicit_joint_balance_boundary_budget (r+4) (r+12) etaBal x hηBal hx).1
  · exact (Classical.choose_spec (marked_vortex_active_transfer_from_parent_fixed_margin r (2*αRef)
      (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) ζFixed levelEta
      (successorWeightUpper k₀ ((2*αRef)/4)) (ρ₀/(800*((r+4:ℕ):ℝ))) hζ hη
      (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le (by positivity) (by positivity))).1
end Oberwolfach
