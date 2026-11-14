module

public import Oberwolfach.FirstVortexReadyCallerWithActualMatching
public import Oberwolfach.FirstVortexCallerMatchingAtParent

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexReadyCallerMatchingAtParent
    (r k₀:ℕ) (αRef ρ₀ ζFixed levelEta etaBal x:ℝ)
    (hα:0<αRef) (hρ:0<ρ₀) (hζ:0<ζFixed) (hη:0<levelEta)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε:ℝ)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεAbs:ε≤εAbs) (hεRob:ε≤εRob)
    (hεsmall:ε≤min ((min αRef (1/2:ℝ)/2/2)*(ρ₀/(800*((r+4:ℕ):ℝ)))) (1/(200*((r+4:ℕ):ℝ)))/128)
    (hεHost:ε≤(2*αRef)/100000) (hm:7≤(r+4))
    (htstarBound:1/(200*((r+4:ℕ):ℝ))≤(1/100)/(((r+4):ℕ):ℝ)) (bmatch ρreserve εBalSelected ζBalSelected δParentSelected:ℝ):Prop :=
    let tstar:ℝ:=1/(200*((r+4:ℕ):ℝ))
    let pstar:ℝ:=ρ₀/(800*((r+4:ℕ):ℝ))
    let BAParent:=successorWeightUpper k₀ ((2*αRef)/4)
    let localCap:=markedExplicitJointLocalCap (r+4) (r+12) etaBal x
    let transferCap:=Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r (2*αRef) tstar pstar ζFixed levelEta BAParent pstar
      hζ hη (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le (by dsimp [pstar]; positivity) (by dsimp [tstar]; positivity));
    let θUpper:ℝ:=1
    let assignUpper:ℝ:=1;
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
    FirstVortexCallerMatchingAtParent r (r+12) k₀ 1 αRef (1/100) (ρ₀/4) (min αRef (1/2:ℝ)/2)
      (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) ρ₀ hρ
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c chosenLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap
      hε hε1 hεAbs hεRob hεsmall (2*αRef) (by positivity) hεHost hm htstarBound bmatch localCap ρreserve εBalSelected ζBalSelected δParentSelected

theorem first_vortex_ready_caller_matching_at_parent
    (r k₀:ℕ) (αRef ρ₀ ζFixed levelEta etaBal x:ℝ)
    (hα:0<αRef) (hρ:0<ρ₀) (hζ:0<ζFixed) (hη:0<levelEta)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε:ℝ)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεAbs:ε≤εAbs) (hεRob:ε≤εRob)
    (hεsmall:ε≤min ((min αRef (1/2:ℝ)/2/2)*(ρ₀/(800*((r+4:ℕ):ℝ)))) (1/(200*((r+4:ℕ):ℝ)))/128)
    (hεHost:ε≤(2*αRef)/100000) (hm:7≤r+4)
    (htstarBound:1/(200*((r+4:ℕ):ℝ))≤(1/100)/(((r+4):ℕ):ℝ)) (bmatch ρreserve:ℝ)
    (εBalSelected ζBalSelected δParentSelected:ℝ)
    (hεBal:0<εBalSelected) (hζBal:0<ζBalSelected) (hδParent:0<δParentSelected)
    (hReady:FirstVortexReadyCallerWithActualMatching r k₀ αRef ρ₀ ζFixed levelEta etaBal x hα hρ hζ hη
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      hε hε1 hεAbs hεRob hεsmall hεHost hm htstarBound bmatch ρreserve):
    FirstVortexReadyCallerMatchingAtParent r k₀ αRef ρ₀ ζFixed levelEta etaBal x hα hρ hζ hη
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      hε hε1 hεAbs hεRob hεsmall hεHost hm htstarBound bmatch ρreserve εBalSelected ζBalSelected δParentSelected :=by
  obtain ⟨δold,δlocal,hold,hold1,hgap,hδlocal,hchosen,hchosenCap,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal,
    hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,hlam,hPack⟩:=hReady
  refine ⟨δold,δlocal,hold,hold1,hgap,hδlocal,hchosen,hchosenCap,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal,
    hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,hlam,?_⟩
  exact first_vortex_caller_matching_at_parent r (r+12) k₀ 1 αRef (1/100) (ρ₀/4) (min αRef (1/2:ℝ)/2)
    (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) ρ₀ hρ
    β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
    cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
    α ε _ _ (min eta globalRate) _ _ 1 δold δlocal _ _ hε hε1 hεAbs hεRob hεsmall
    (2*αRef) (by positivity) hεHost hm htstarBound bmatch _ ρreserve εBalSelected ζBalSelected δParentSelected
    hεBal hζBal hδParent hPack
end Oberwolfach
