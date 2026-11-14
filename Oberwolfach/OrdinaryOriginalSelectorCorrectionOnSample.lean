module

public import Oberwolfach.OrdinaryOriginalSelectorCallback
public import Oberwolfach.OrdinaryAssignedCorrectionProbabilityShape

@[expose] public section
/-! Apply the original matching selector's callback to the correction
callback on the very same assigned sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_selector_correction_on_sample
    (r d:ℕ) (hd:2≤d) (mAbs a b t f q₀ N Nc Ng Nh Ncol:ℕ)
    (αcorr pstar ω εabs εv L ξ ζlocal χlocal χglobal χhub χcol C:ℝ)
    (hcorr:OrdinaryWeightedCorrectionAfterLocalThresholds r d hd mAbs a b t f q₀ N Nc Ng Nh Ncol
      αcorr pstar ω εabs εv L ξ ζlocal χlocal χglobal χhub χcol C)
    (n qCount K D:ℕ) (hn:N≤n) (hng:Ng≤n) (hωn:ω*n≤(qCount:ℝ)) (hqn:qCount≤n) (hD:0<D)
    (P Bad:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D)
    (hdegree:(cycleThreshold r+αcorr)*n≤D) (hBad:∀v,(Bad.degree v:ℝ)≤L)
    (π:Equiv.Perm (Fin n)) (hconf:permutationConflictGraph π (3*d)≤Bad)
    (hnoshort:∀x k,0<k→k<2*d+1→(π^k) x≠x)
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ ρ₀ smin:ℝ) (mMatch:ℕ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin d)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D)
    (hhalf:(1/2:ℝ)*(n:ℝ)≤D) (hpstar:2*pstar≤ρ₀*smin)
    (A Z Wterm W:Finset (Fin n)) (Bterm B Htest:Finset (Fin qCount))
    (hA:A=Finset.univ\Z) (hZ:(Z.card:ℝ)≤εabs*n)
    (hsize:Wterm.card+Bterm.card≤t) (hWW:Wterm⊆W) (hBB:Bterm⊆B) (hW:W.card≤f)
    (hB:(B.card:ℝ)≤εabs*n+f) (hZv:(Z.card:ℝ)≤εv*n) (hBv:(B.card:ℝ)≤εv*n+f)
    (hNc:Nc≤Z.card) (hNh:Nh≤Z.card) (hNcol:Ncol≤Z.card)
    (hHpos:0<Htest.card) (hHle:Htest.card≤Z.card) (hHC:(Htest.card:ℝ)≤C*Z.card)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
    (ζ χpair χlist χbal χbd χnbr χpairR χpath:ℝ)
    (Cres:∀u,Finset (F u).ConnectedComponent)
    (lamMatch aRow γrow σbal aEvent ζDel lamList bMatch:ℝ)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (seed:(Fin (mMatch+1)→Fin n)→ℝ) (tMatch ξMatch:ℝ)
    (rstar k:ℕ) (τ α:ℝ) (BO:Fin K→ℝ)
    (hselector:OrdinaryOriginalSelectorCallback n qCount D rstar mMatch k d K hd
      ρ₀ θ lamMatch aRow γrow lamList ζDel smin τ tMatch ξMatch bMatch σbal
      ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent α BO F hF P π i₀ rsv Cres sampling w seed):
    OrdinaryAssignedCorrectionProbabilityShape r d mAbs a b t q₀ n qCount K D hd
      ζlocal χlocal χglobal χhub χcol ξ P Bad π F hF i₀ rsv θ ρ₀ smin mMatch sampling
      A Z Wterm Bterm B Htest R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres
      lamMatch aRow γrow σbal aEvent ζDel lamList bMatch w seed tMatch ξMatch :=by
  have hs:=hselector ρ (fun _=>True) 0
  have hc:=hcorr n qCount K D hn hng hωn hqn hD P Bad hreg hdegree hBad π hconf hnoshort
    F hF i₀ rsv θ ρ₀ smin mMatch sampling hρ hρlo hhalf hpstar
    A Z Wterm W Bterm B Htest hA hZ hsize hWW hBB hW hB hZv hBv hNc hNh hNcol hHpos hHle hHC
    ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lamMatch aRow γrow σbal aEvent ζDel lamList bMatch
    w seed tMatch ξMatch
  exact hc hs
end Oberwolfach
