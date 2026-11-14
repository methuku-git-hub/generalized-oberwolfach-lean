module

public import Oberwolfach.OrdinaryCorrectionRatesFromOriginalAssumptions
public import Oberwolfach.OrdinaryCorrectionAllLocalVortexThresholds

@[expose] public section
/-! Original host and abundance assumptions give the correction rates and
all local-test sizes on the same first vortex level. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_first_vortex_correction_inputs
    (θhost α ρ₀ βfreq ε εabs εv:ℝ) (hθ:(1/2:ℝ) ≤ θhost) (hα:0<α)
    (hρ₀:0<ρ₀) (hρ₀1:ρ₀ ≤ 1) (hβ:0<βfreq) (hβ1:βfreq ≤ 1)
    (hε:0<ε) (habs:ε ≤ εabs) (hv:ε ≤ εv) (Nc Ng Nh Ncol:ℕ):
    ∃N:ℕ,1 ≤ N ∧ ∀{n qCount D K mv:ℕ},N ≤ n → 0<mv → qCount ≤ n → 
    ∀(P:SimpleGraph (Fin n)),P.IsRegularOfDegree D → (θhost+α)*(n:ℝ) ≤ D → 
    ρ₀ ≤ initialIndexDensity (Fin qCount) D → initialIndexDensity (Fin qCount) D ≤ 1 → 
    ∀(F:Fin qCount → SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (rstar:ℕ),
    (∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v)) ≤ θhost) → 
    (∀w,βfreq*n ≤ ((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ)) → 
    ∀(i₀:Fin K) (rsv θ c βv:ℝ) (d:ℕ)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ (βfreq/200) d)
      (Q:Vortex (Fin qCount) P D βv ε mv),0 ≤ βv → βv ≤ 1/4 → 
    let smin:=βfreq/200;let pstar:=ρ₀*smin/2;let ω:=ρ₀/4
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let Z:=Q.extendedVertices 1;let Htest:=Q.extendedIndices 1;
    (0<smin ∧ 0<pstar ∧ pstar ≤ 1 ∧ 0<ω ∧ 0<D ∧
      (cycleThreshold rstar+α/2)*(n:ℝ) ≤ D ∧ ω*n ≤ (qCount:ℝ) ∧
      pstar ≤ p ∧ pstar ≤ 2*p ∧ pstar ≤ rsv ∧ rsv ≤ 1 ∧
      2*p=initialIndexDensity (Fin qCount) D*rsv ∧
      (∀w,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w false=rsv) ∧
      (∀w,ordinaryAssignedMarkedProbability F hF K θ c w false=0)) ∧
    (Ng ≤ n ∧ Nc ≤ Z.card ∧ Nh ≤ Z.card ∧ Ncol ≤ Z.card ∧
      0<Htest.card ∧ Htest.card ≤ Z.card ∧ (Htest.card:ℝ) ≤ (2/ε)*Z.card ∧
      (Z.card:ℝ) ≤ εabs*n ∧ (Htest.card:ℝ) ≤ εabs*n ∧
      (Z.card:ℝ) ≤ εv*n ∧ (Htest.card:ℝ) ≤ εv*n) :=by
  obtain ⟨N,hN,hgeometry⟩:=ordinary_correction_all_local_vortex_thresholds ε εabs εv hε habs hv Nc Ng Nh Ncol
  refine ⟨N,hN,?_⟩
  intro n qCount D K mv hn hmv hq P hreg hdegree hρlo hρhi F hF rstar hthreshold habundance
    i₀ rsv θ c βv d sampling Q hβv hβv1 smin pstar ω p Z Htest
  have hn0:0<n:=by omega
  have hrates:=ordinary_correction_rates_from_original_assumptions θhost α ρ₀ βfreq hθ hα hρ₀ hρ₀1 hβ hβ1
    hn0 P hreg hdegree hρlo F hF rstar hthreshold habundance i₀ rsv θ c d sampling
  obtain ⟨hs,hp,hp1,hω,hD,hmargin,hrest⟩:=hrates
  have hhalf:(n:ℝ)/2 ≤ D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ θhost+α by linarith) (show (0:ℝ) ≤ n by positivity)
    nlinarith [hdegree,hh]
  have hgeom:=hgeometry P D mv βv ρ₀ Q hreg (by simpa using hn0) hD (by simpa using hhalf) hmv
    hρ₀ hρlo hρhi hβv hβv1 (by simpa using hq) (by simpa using hn)
  refine ⟨⟨hs,hp,hp1,hω,hD,hmargin,hrest⟩,?_⟩
  simpa only [Fintype.card_fin] using hgeom
end Oberwolfach
