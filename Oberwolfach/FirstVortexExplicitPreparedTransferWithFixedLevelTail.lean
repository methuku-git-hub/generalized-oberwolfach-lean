module

public import Oberwolfach.FirstVortexExplicitPreparedTransferWithLevelAnchoredTail
public import Oberwolfach.FirstVortexCallerPreparedChainWithFixedLevelTail

@[expose] public section
/-! The probability tail uses fixed parent-aligned level witnesses and the
same prepared matching choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 90000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

def FirstVortexExplicitPreparedTransferWithFixedLevelTail
    (r k₀:ℕ) (αRef ρ₀ ζFixed levelEta etaBal x:ℝ)
    (hα:0<αRef) (hρ:0<ρ₀) (hζ:0<ζFixed) (hη:0<levelEta)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch:ℝ)
    (h Qpow:ℕ) (sstar ω γRich tailTstar kstar:ℝ)
    (βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (hm:7≤r+4) (htstarBound:tailTstar≤(1/100)/(((r+4):ℕ):ℝ)) (gammaStep sigmaStep κmax δparent εBal ζBal:ℝ):Prop :=
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
    (∃(hε:0<ε) (hε1:ε<1/4) (hεAbs:ε≤εAbs) (hεRob:ε≤εRob)
       (hεsmall:ε≤min ((γRich/2)*kstar) tailTstar/128),
      FirstVortexCallerPreparedChainWithFixedLevelTail r h k₀ Qpow ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
        α ε c c localCap (min eta globalRate) active θcap 1 δold δlocal lamCap κCap bmatch
        αRef sstar ω γRich tailTstar kstar hρ βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
        hε hε1 hεAbs hεRob hεsmall hm htstarBound gammaStep sigmaStep κmax δparent εBal ζBal) ∧
    FirstVortexCallerParametersPrepared r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c localCap (min eta globalRate) active θcap 1 δold δlocal lamCap κCap bmatch
theorem first_vortex_explicit_prepared_transfer_with_fixed_level_tail
    (r k₀:ℕ) (αRef ρ₀ ζFixed levelEta etaBal x:ℝ)
    (hα:0<αRef) (hρ:0<ρ₀) (hζ:0<ζFixed) (hη:0<levelEta)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch:ℝ)
    (h Qpow:ℕ) (sstar ω γRich tailTstar kstar:ℝ)
    (βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (hm:7≤r+4) (htstarBound:tailTstar≤(1/100)/(((r+4):ℕ):ℝ)) (gammaStep sigmaStep:ℝ)
    (κmax δparent εBal ζBal:ℝ) (hκmax:0<κmax) (hδparent:0<δparent) (hεBal:0<εBal) (hζBal:0<ζBal)
    (hPrepared:FirstVortexExplicitPreparedTransferWithLevelAnchoredTail r k₀ αRef ρ₀ ζFixed levelEta etaBal x hα hρ hζ hη
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch
      h Qpow sstar ω γRich tailTstar kstar βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable hm htstarBound gammaStep sigmaStep):
    FirstVortexExplicitPreparedTransferWithFixedLevelTail r k₀ αRef ρ₀ ζFixed levelEta etaBal x hα hρ hζ hη
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε δold δlocal bmatch
      h Qpow sstar ω γRich tailTstar kstar βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable hm htstarBound gammaStep sigmaStep κmax δparent εBal ζBal:=by
  dsimp only [FirstVortexExplicitPreparedTransferWithLevelAnchoredTail] at hPrepared
  dsimp only [FirstVortexExplicitPreparedTransferWithFixedLevelTail]
  obtain ⟨hchosen,hchosenLocal,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal,
    hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,hlam,hchain,hexact⟩:=hPrepared
  obtain ⟨hε,hε1,hεAbs,hεRob,hεsmall,hchain⟩:=hchain
  refine ⟨hchosen,hchosenLocal,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal,
    hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,hlam,?_,hexact⟩
  refine ⟨hε,hε1,hεAbs,hεRob,hεsmall,?_⟩
  exact first_vortex_caller_prepared_chain_with_fixed_level_tail r h k₀ Qpow ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
    α ε _ _ _ (min eta globalRate) _ _ 1 δold δlocal _ _ bmatch
    αRef sstar ω γRich tailTstar kstar hρ βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
    hε hε1 hεAbs hεRob hεsmall hm htstarBound gammaStep sigmaStep κmax δparent εBal ζBal hκmax hδparent hεBal hζBal hchain
end Oberwolfach
