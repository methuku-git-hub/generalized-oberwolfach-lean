module

public import Oberwolfach.OrdinaryDeepReservedOriginalHostBounds

@[expose] public section
/-! The full-parent selector's host threshold follows from the same original
abundance and degree hypotheses, with half the original margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_parent_reserved_original_host_bounds
    (n D q rstar:ℕ) (θhost α ρ₀ βfreq:ℝ)
    (hr:3≤rstar) (hn:0<n) (hα:0<α) (hρ:0<ρ₀) (hβ:0<βfreq) (hθ:(1/2:ℝ)≤θhost)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin q) D)
    (F:Fin q→SimpleGraph (Fin n))
    (hthreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θhost)
    (habundance:∀w,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ))
    (hdegree:(θhost+α)*(n:ℝ)≤D):
    (max (1/2) (cycleThreshold ((rstar-1)+1))+2*(α/2))*(n:ℝ)≤D :=by
  obtain ⟨hcycle,_⟩:=ordinary_deep_reserved_original_host_bounds n D q rstar θhost α ρ₀ βfreq
    hr hn hα hρ hβ hρlo F hthreshold habundance hdegree
  have hmax:max (1/2) (cycleThreshold ((rstar-1)+1))≤θhost:=max_le hθ hcycle
  have hn0:(0:ℝ)≤n:=by positivity
  have hh:=mul_le_mul_of_nonneg_right hmax hn0
  nlinarith [hdegree]
end Oberwolfach
