module

public import Oberwolfach.OrdinaryProtectedPreparationFeasible
public import Oberwolfach.OrdinaryParentSelectorOriginalMargins

@[expose] public section
/-! The auxiliary parent-selector margin can be assumed in the proof: if it
fails, the original host and abundant factors cannot exist. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_preparation_from_feasible
    (hfeasible:OrdinaryProtectedPreparationFeasible):OrdinaryProtectedPreparation :=by
  intro θ α₀ εmax ρstar β hθ hθ1 hα hε hρstar hρ1 hβ hβ1 rstar hr
  by_cases hmargin:α₀/2≤1/2 ∧ max (1/2) (cycleThreshold rstar)+(α₀/2)/2≤1
  · exact hfeasible θ α₀ εmax ρstar β hθ hθ1 hα hε hρstar hρ1 hβ hβ1 rstar hr hmargin
  · refine ⟨1,by norm_num,?_⟩
    intro χ hχ hχ1
    refine ⟨1,2,by omega,by omega,?_⟩
    intro n hn P D q hreg hEven hdegree ρ hρlo hρhi F hF hthreshold habundance
    have hnpos:0<n:=by omega
    have hρlo':ρstar ≤ initialIndexDensity (Fin q) D:=by simpa [ρ,initialIndexDensity] using hρlo
    have hh:=ordinary_parent_selector_original_margins n D q rstar θ α₀ ρstar β hr hnpos hα hρstar hβ hθ
      hρlo' F hthreshold habundance P hreg hdegree
    have heq:(rstar-1)+1=rstar:=by omega
    rw [heq] at hh
    exact False.elim (hmargin hh)
end Oberwolfach
