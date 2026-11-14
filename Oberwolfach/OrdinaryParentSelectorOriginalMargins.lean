module

public import Oberwolfach.OrdinaryDeepReservedOriginalHostBounds
public import Oberwolfach.VortexSizeBounds

@[expose] public section
/-! Whenever the original host and abundant factors exist, the auxiliary
parent selector's upper-margin hypotheses hold automatically. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_parent_selector_original_margins
    (n D q rstar:ℕ) (θhost α ρ₀ βfreq:ℝ)
    (hr:3≤rstar) (hn:0<n) (hα:0<α) (hρ:0<ρ₀) (hβ:0<βfreq) (hθ:(1/2:ℝ)≤θhost)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin q) D)
    (F:Fin q→SimpleGraph (Fin n))
    (hthreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θhost)
    (habundance:∀w,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ))
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (hdegree:(θhost+α)*(n:ℝ)≤D):
    α/2≤1/2 ∧ max (1/2) (cycleThreshold ((rstar-1)+1))+(α/2)/2≤1 :=by
  obtain ⟨hcycle,_⟩:=ordinary_deep_reserved_original_host_bounds n D q rstar θhost α ρ₀ βfreq
    hr hn hα hρ hβ hρlo F hthreshold habundance hdegree
  have hmax:max (1/2) (cycleThreshold ((rstar-1)+1))≤θhost:=max_le hθ hcycle
  have hD:=regular_degree_le_card hreg (by simpa using hn)
  have hDn:D≤n:=by simpa using hD
  have hD':(D:ℝ)≤n:=by exact_mod_cast hDn
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn
  have hsum:θhost+α≤1:=by nlinarith [hdegree,hD']
  constructor <;> linarith
end Oberwolfach
