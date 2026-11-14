module

public import Oberwolfach.OrdinaryOriginalFirstVortexCorrectionInputs

@[expose] public section
/-! The first-vortex correction consequences at a fixed size threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryFirstVortexCorrectionThresholdShape
    (N Nc Ng Nh Ncol:ℕ) (θhost α ρ₀ βfreq ε εabs εv:ℝ):Prop :=
    ∀{n qCount D K mv:ℕ},N ≤ n → 0<mv → qCount ≤ n → 
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
      (Z.card:ℝ) ≤ εv*n ∧ (Htest.card:ℝ) ≤ εv*n)
end Oberwolfach
