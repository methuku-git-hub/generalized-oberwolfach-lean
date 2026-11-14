module

public import Oberwolfach.OrdinaryOriginalSelectorFactorWitness
public import Oberwolfach.OrdinaryFirstVortexCorrectionPointShape

@[expose] public section
/-! Choose the original factor selector and derive first-vortex correction
rates for its actual index, reserve, and sampling law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_selector_with_vortex_inputs
    (n qCount D rstar m k d K mv Nc Ng Nh Ncol Nsel Ngeom:ℕ) (hd:2≤d)
    (βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a ε εabs εv βv:ℝ)
    (BO:Fin K→ℝ)
    (hsel:OrdinaryOriginalThresholdForAllFactors rstar m k d K hd Nsel βfreq ρ₀ α θ θhost
      lam aRow γ cap lamList ζDel (βfreq/200) τ t ξ b BO ζ χpair χlist σ χbal χbd χnbr χpairR χpath a)
    (hgeom:OrdinaryFirstVortexCorrectionThresholdShape Ngeom Nc Ng Nh Ncol θhost α ρ₀ βfreq ε εabs εv)
    (hnsel:Nsel≤n) (hngeom:Ngeom≤n) (hn:2≤n) (hq:qCount≤n) (hmv:0<mv)
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (habundance:∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ))
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D) (hρhi:initialIndexDensity (Fin qCount) D≤1)
    (hthreshold:∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θhost)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (π:Equiv.Perm (Fin n))
    (hdegree:(θhost+α)*(n:ℝ)≤D) (hθ:(1/2:ℝ)≤θhost) (hα:0<α)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (Q:Vortex (Fin qCount) P D βv ε mv) (hβv:0≤βv) (hβv1:βv≤1/4):
    ∃(i₀:Fin K) (rsv:ℝ) (C:∀u,Finset (F u).ConnectedComponent)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ (βfreq/200) d)
      (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
      (seed:(Fin (m+1)→Fin n)→ℝ),
      OrdinaryOriginalSelectorFactorWitness n qCount D rstar m k d K hd
        ρ₀ θ lam aRow γ lamList ζDel (βfreq/200) τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a α
        BO F hF P π i₀ rsv C sampling w seed ∧
      OrdinaryFirstVortexCorrectionPointShape n qCount D K mv d rstar Nc Ng Nh Ncol
        θhost α ρ₀ βfreq ε εabs εv P F hF i₀ rsv θ ((m:ℝ)+1) βv Q :=by
  have hnR:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith) (le_of_lt hnR)
  have hDreal:(0:ℝ)<D:=by nlinarith [hdegree]
  have hD:0<D:=by exact_mod_cast hDreal
  obtain ⟨i₀,rsv,C,hi,hrsv,hrsv1,hcand,hCsize,hCrsv,hCfreq,sampling,w,seed,hw,hwdecomp,hwzero,hseed,hselector⟩:=
    hsel n hnsel hn (Fin qCount) (by simpa using hq) F hF habundance D hD hρlo hρhi hthreshold P hreg π hdegree hnoshort
  have hg:=hgeom hngeom hmv hq P hreg hdegree hρlo hρhi F hF rstar hthreshold habundance
    i₀ rsv θ ((m:ℝ)+1) βv d sampling Q hβv hβv1
  refine ⟨i₀,rsv,C,sampling,w,seed,?_,?_⟩
  · exact ⟨hi,hrsv,hrsv1,hcand,hCsize,hCrsv,hCfreq,hw,hwdecomp,hwzero,hseed,hselector⟩
  · exact hg
end Oberwolfach
