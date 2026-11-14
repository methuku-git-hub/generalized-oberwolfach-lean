module

public import Oberwolfach.OrdinaryAssignedCorrectionOriginalRateChoice
public import Oberwolfach.OrdinaryAbundanceThresholdFromOriginal

@[expose] public section
/-! Original host degree, abundant cycle class and assigned law provide the
correction theorem's density and threshold inputs with fixed early rates. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_correction_rates_from_original_assumptions
    (θhost α ρ₀ βfreq:ℝ) (hθ:(1/2:ℝ) ≤ θhost) (hα:0<α)
    (hρ₀:0<ρ₀) (hρ₀1:ρ₀ ≤ 1) (hβ:0<βfreq) (hβ1:βfreq ≤ 1)
    {n qCount D K:ℕ} (hn:0<n)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D)
    (hdegree:(θhost+α)*(n:ℝ) ≤ D) (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D)
    (F:Fin qCount → SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (rstar:ℕ)
    (hthreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v)) ≤ θhost)
    (habundance:∀w,βfreq*n ≤ ((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ))
    (i₀:Fin K) (rsv θ c:ℝ) (d:ℕ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ (βfreq/200) d):
    let smin:=βfreq/200
    let pstar:=ρ₀*smin/2
    let ω:=ρ₀/4
    let p:=initialIndexDensity (Fin qCount) D*rsv/2;
    0<smin ∧ 0<pstar ∧ pstar ≤ 1 ∧ 0<ω ∧ 0<D ∧
    (cycleThreshold rstar+α/2)*(n:ℝ) ≤ D ∧ ω*n ≤ (qCount:ℝ) ∧
    pstar ≤ p ∧ pstar ≤ 2*p ∧ pstar ≤ rsv ∧ rsv ≤ 1 ∧
    2*p=initialIndexDensity (Fin qCount) D*rsv ∧
    (∀w,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w false=rsv) ∧
    (∀w,ordinaryAssignedMarkedProbability F hF K θ c w false=0) :=by
  intro smin pstar ω p
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn
  have hdegreeHalf:(1/2:ℝ)*(n:ℝ) ≤ D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ θhost+α by linarith) hnR.le
    exact hh.trans hdegree
  have hD:0<D:=by
    have hh:(0:ℝ)<D:=(mul_pos (by norm_num) hnR).trans_le hdegreeHalf
    exact_mod_cast hh
  have hρlo':ρ₀ ≤ 2*(qCount:ℝ)/(D:ℝ):=by simpa [initialIndexDensity] using hρlo
  have hcycle:=ordinary_abundance_threshold_from_original θhost ρ₀ βfreq hρ₀ hβ n D qCount rstar hn hρlo' F hthreshold habundance
  have hmargin:(cycleThreshold rstar+α/2)*(n:ℝ) ≤ D:=by
    have hh:=mul_le_mul_of_nonneg_right (show cycleThreshold rstar+α/2 ≤ θhost+α by linarith) hnR.le
    exact hh.trans hdegree
  obtain ⟨hs,hp,hp1,hω,hbase⟩:=ordinary_assigned_correction_original_rate_choice βfreq ρ₀ hβ hβ1 hρ₀ hρ₀1
  have h:=hbase F hF P hreg hD i₀ rsv θ c d hρlo hdegreeHalf sampling
  refine ⟨hs,hp,hp1,hω,hD,hmargin,?_⟩
  simpa only [Fintype.card_fin] using h
end Oberwolfach
