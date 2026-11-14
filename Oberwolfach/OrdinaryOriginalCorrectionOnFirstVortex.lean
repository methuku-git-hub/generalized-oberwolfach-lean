module

public import Oberwolfach.OrdinaryOriginalSelectorCorrectionOnSample
public import Oberwolfach.OrdinaryOriginalSelectorCallbackFromWitness
public import Oberwolfach.OrdinaryFirstVortexCorrectionPointShape
public import Oberwolfach.OrdinaryFirstVortexTerminalCorrectionInputs
public import Oberwolfach.PermutationConflictDegree

@[expose] public section
/-! Instantiate the correction join at the actual first and terminal vortex
levels and the actual permutation conflict graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_correction_on_first_vortex
    (n qCount D rstar m k d K mv mAbs aAbs bAbs q₀ Ncorr Nc Ng Nh Ncol:ℕ) (hd:2≤d)
    (βfreq ρ₀ α θ θhost lam aRow γ lamList ζDel τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent ε εabs εv βv ξAbs χlocal χglobal χhub χcol:ℝ)
    (BO:Fin K→ℝ)
    (hcorr:OrdinaryWeightedCorrectionAfterLocalThresholds rstar d hd mAbs aAbs bAbs (2*mv) mv q₀ Ncorr Nc Ng Nh Ncol
      (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) εabs εv (2*((3*d:ℕ):ℝ)) ξAbs (θ/2) χlocal χglobal χhub χcol (2/ε))
    (hncorr:Ncorr≤n) (hn:2≤n) (hq:qCount≤n) (hρ:0<ρ₀) (he:0<ε)
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (π:Equiv.Perm (Fin n))
    (hdegree:(θhost+α)*(n:ℝ)≤D) (hθ:(1/2:ℝ)≤θhost) (hα:0<α)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D) (hρhi:initialIndexDensity (Fin qCount) D≤1)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (Q:Vortex (Fin qCount) P D βv ε mv)
    (i₀:Fin K) (rsv:ℝ) (Cres:∀u,Finset (F u).ConnectedComponent)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ (βfreq/200) d)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (seed:(Fin (m+1)→Fin n)→ℝ)
    (hwitness:OrdinaryOriginalSelectorFactorWitness n qCount D rstar m k d K hd
      ρ₀ θ lam aRow γ lamList ζDel (βfreq/200) τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent α
      BO F hF P π i₀ rsv Cres sampling w seed)
    (hgeom:OrdinaryFirstVortexCorrectionPointShape n qCount D K mv d rstar Nc Ng Nh Ncol
      θhost α ρ₀ βfreq ε εabs εv P F hF i₀ rsv θ ((m:ℝ)+1) βv Q)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)):
    OrdinaryAssignedCorrectionProbabilityShape rstar d mAbs aAbs bAbs (2*mv) q₀ n qCount K D hd
      (θ/2) χlocal χglobal χhub χcol ξAbs P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) m sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1)
      R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lam aRow γ σ aEvent ζDel lamList bMatch w seed tMatch ξMatch :=by
  obtain ⟨⟨hs,hp,hp1,hω,hD,hmargin,hωn,hrest⟩,
    hNg,hNc,hNh,hNcol,hHpos,hHle,hHC,hZabs,hBabs,hZv,hBv⟩:=hgeom
  have hnpos:0<n:=by omega
  have hnR:(0:ℝ)<n:=by exact_mod_cast hnpos
  have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith) (le_of_lt hnR)
  have hhalf:(1/2:ℝ)*(n:ℝ)≤D:=by linarith [hdegree]
  have hterminal:=ordinary_first_vortex_terminal_correction_inputs P Q hreg hnpos hD he.le hρhi hZabs hBabs hZv hBv
  obtain ⟨hsize,hWsub,hBsub,hWsize,_,hBsmall,_,hBvsmall⟩:=hterminal
  have hBad:∀v,((permutationConflictGraph π (3*d)).degree v:ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro v
    exact_mod_cast permutationConflictGraph_degree_le π (3*d) v
  have hpstar:2*(ρ₀*(βfreq/200)/2)≤ρ₀*(βfreq/200):=by ring_nf; exact le_rfl
  have hselector:OrdinaryOriginalSelectorCallback n qCount D rstar m k d K hd
    ρ₀ θ lam aRow γ lamList ζDel (βfreq/200) τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent α
    BO F hF P π i₀ rsv Cres sampling w seed :=
    ordinary_original_selector_callback_from_witness n qCount D rstar m k d K hd
    ρ₀ θ lam aRow γ lamList ζDel (βfreq/200) τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent α
    BO F hF P π i₀ rsv Cres sampling w seed hwitness
  exact ordinary_original_selector_correction_on_sample rstar d hd mAbs aAbs bAbs (2*mv) mv q₀ Ncorr Nc Ng Nh Ncol
    (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) εabs εv (2*((3*d:ℕ):ℝ)) ξAbs (θ/2) χlocal χglobal χhub χcol (2/ε) hcorr
    n qCount K D hncorr hNg hωn hq hD P (permutationConflictGraph π (3*d)) hreg hmargin hBad π le_rfl hnoshort
    F hF i₀ rsv θ ρ₀ (βfreq/200) m sampling hρ hρlo hhalf hpstar
    (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length) (Q.extendedVertices Q.length)
    (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1)
    rfl hZabs hsize (Finset.Subset.rfl) hBsub hWsize hBsmall hZv hBvsmall hNc hNh hNcol hHpos hHle hHC
    R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lam aRow γ σ aEvent ζDel lamList bMatch w seed tMatch ξMatch
    rstar k τ α BO hselector
end Oberwolfach
