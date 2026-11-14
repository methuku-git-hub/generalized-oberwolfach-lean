module

public import Oberwolfach.OrdinaryAbundanceThresholdFromOriginal
public import Oberwolfach.Vortex
public import Oberwolfach.TwoComponentLower

@[expose] public section
/-! The original abundance and threshold assumptions force the host
threshold to be at least one half. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_host_threshold_half
    (n D q rstar:ℕ) (θhost ρ₀ βfreq:ℝ) (hr:3≤rstar) (hn:0<n)
    (hρ:0<ρ₀) (hβ:0<βfreq) (hρlo:ρ₀ ≤ initialIndexDensity (Fin q) D)
    (F:Fin q→SimpleGraph (Fin n))
    (hthreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θhost)
    (habundance:∀w,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ)):
    (1/2:ℝ)≤θhost :=by
  have hρlo':ρ₀≤2*(q:ℝ)/(D:ℝ):=by simpa [initialIndexDensity] using hρlo
  exact (cycleThreshold_half_le hr).trans
    (ordinary_abundance_threshold_from_original θhost ρ₀ βfreq hρ hβ n D q rstar hn hρlo' F hthreshold habundance)
end Oberwolfach
