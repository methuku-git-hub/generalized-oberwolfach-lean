module

public import Oberwolfach.FirstVortexExplicitPreparedTransferBothBudgets
public import Oberwolfach.FirstVortexCallerPreparedWithChain

@[expose] public section
/-! The exact level caps carry the prepared solver and its fixed-terminal
chain threshold under the original matching and ambient rate data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 60000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexExplicitPreparedTransferWithChain
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
    FirstVortexCallerPreparedWithChain r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c c localCap (min eta globalRate) active θcap 1 δold δlocal lamCap κCap bmatch ∧
    FirstVortexCallerParametersPrepared r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c localCap (min eta globalRate) active θcap 1 δold δlocal lamCap κCap bmatch

theorem first_vortex_explicit_prepared_transfer_with_chain
    (r k₀:ℕ) (αRef ρ₀ ζFixed levelEta etaBal x:ℝ)
    (hα:0<αRef) (hρ:0<ρ₀) (hζ:0<ζFixed) (hη:0<levelEta)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch:ℝ)
    (βList εLevel εAbs εRob γRich kstar tstar hostCap:ℝ)
    (hInitial:FirstVortexInitialMatchingVortexRates ρ₀ δglobal βList βfinal εLevel εInner εAbs εRob γRich kstar tstar hostCap bmatch α ε)
    (hδold:0<δold) (hδold1:δold≤1) (hρone:ρ₀≤1) (hm:7≤r+4)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho) (hβ:0<βfinal) (hβone:βfinal≤1)
    (h:FirstVortexExplicitPreparedTransferBothBudgets r k₀ αRef ρ₀ ζFixed levelEta etaBal x hα hρ hζ hη
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch):
    FirstVortexExplicitPreparedTransferWithChain r k₀ αRef ρ₀ ζFixed levelEta etaBal x hα hρ hζ hη
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch:=by
  dsimp only [FirstVortexExplicitPreparedTransferBothBudgets] at h
  dsimp only [FirstVortexExplicitPreparedTransferWithChain]
  obtain ⟨hchosen,hchosenLocal,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal,
    hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,hlam,hsmall,hexact⟩:=h
  refine ⟨hchosen,hchosenLocal,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal,
    hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,hlam,?_,hexact⟩
  apply first_vortex_caller_prepared_with_chain r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
    α ε _ _ _ (min eta globalRate) _ _ 1 δold δlocal _ _ bmatch
    βList εLevel εAbs εRob γRich kstar tstar hostCap hInitial hδold hδold1 hρ hρone hm hθold32 hθ100 hrho heta hetaR hβ hβone ?_ hsmall
  exact (min_le_left _ _).trans hchosenLocal
end Oberwolfach
