module

public import Oberwolfach.OrdinaryAbundanceThresholdFromOriginal
public import Oberwolfach.Vortex

@[expose] public section
/-! The reserved wheel used in the all-level construction has a threshold
and host margin inherited from the original factor assumptions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_reserved_original_host_bounds
    (n D q rstar:ℕ) (θhost α ρ₀ βfreq:ℝ)
    (hr:3≤rstar) (hn:0<n) (hα:0<α) (hρ:0<ρ₀) (hβ:0<βfreq)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin q) D)
    (F:Fin q→SimpleGraph (Fin n))
    (hthreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θhost)
    (habundance:∀w,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ))
    (hdegree:(θhost+α)*(n:ℝ)≤D):
    cycleThreshold ((rstar-1)+1)≤θhost ∧ (θhost+α/2)*(n:ℝ)≤D :=by
  have hρlo':ρ₀≤2*(q:ℝ)/(D:ℝ):=by simpa [initialIndexDensity] using hρlo
  have ht:=ordinary_abundance_threshold_from_original θhost ρ₀ βfreq hρ hβ n D q rstar hn hρlo' F hthreshold habundance
  have heq:(rstar-1)+1=rstar:=by omega
  rw [heq]
  refine ⟨ht,?_⟩
  have hn0:(0:ℝ)≤n:=by positivity
  have hm:=mul_nonneg (show (0:ℝ)≤α/2 by positivity) hn0
  nlinarith [hdegree]
end Oberwolfach
