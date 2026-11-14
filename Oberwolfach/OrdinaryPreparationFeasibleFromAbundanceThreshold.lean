module

public import Oberwolfach.OrdinaryPreparationFromFeasible
public import Oberwolfach.OrdinaryAbundanceThresholdFromOriginal

@[expose] public section
/-! It is enough to prove feasible preparation in the branch where the
reserved cycle threshold is below θ: the original abundance assumptions
make the other branch impossible. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryProtectedPreparationFeasibleThreshold : Prop :=
  ∀(θ α₀ εmax ρstar β:ℝ),
    (1/2:ℝ)≤θ→θ<1→0<α₀→0<εmax→∀(hρstar:0<ρstar),ρstar≤1→0<β→β≤1→
  ∀rstar:ℕ,3≤rstar→
  (α₀/2≤1/2 ∧ max (1/2) (cycleThreshold rstar)+(α₀/2)/2≤1)→
  cycleThreshold rstar≤θ→
  ∃ξ:ℝ,0<ξ ∧ ∀χ:ℝ,0<χ→χ<1→∃B N:ℕ,1≤B ∧ 1≤N ∧
  ∀n≥N,∀(P:SimpleGraph (Fin n)) (D q:ℕ),
    P.IsRegularOfDegree D→Even D→(θ+α₀)*(n:ℝ)≤D→
  let ρ:ℝ:=2*(q:ℝ)/(D:ℝ);
  ∀(hρlo:ρstar≤ρ) (hρhi:ρ≤1),
  ∀F:Fin q→SimpleGraph (Fin n),
    (∀w,(F w).IsRegularOfDegree 2)→
    (∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ)→
    (∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ))→
  ∃I:Finset (Fin n), (I.card:ℝ)≤εmax*n ∧
    1-χ-1/(n:ℝ)^10≤
      (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ
        (hρstar.le.trans hρlo) hρhi)).probability
        (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F)

theorem ordinary_preparation_feasible_from_abundance_threshold
    (hfeasible:OrdinaryProtectedPreparationFeasibleThreshold):OrdinaryProtectedPreparationFeasible :=by
  intro θ α₀ εmax ρstar β hθ hθ1 hα hε hρstar hρ1 hβ hβ1 rstar hr hmargin
  by_cases hcycle:cycleThreshold rstar≤θ
  · exact hfeasible θ α₀ εmax ρstar β hθ hθ1 hα hε hρstar hρ1 hβ hβ1 rstar hr hmargin hcycle
  · refine ⟨1,by norm_num,?_⟩
    intro χ hχ hχ1
    refine ⟨1,2,by omega,by omega,?_⟩
    intro n hn P D q hreg hEven hdegree ρ hρlo hρhi F hF hthreshold habundance
    have hnpos:0<n:=by omega
    have hρlo':ρstar≤2*(q:ℝ)/(D:ℝ):=by simpa [ρ] using hρlo
    exact False.elim (hcycle (ordinary_abundance_threshold_from_original θ ρstar β hρstar hβ
      n D q rstar hnpos hρlo' F hthreshold habundance))
theorem ordinary_preparation_from_abundance_threshold
    (hfeasible:OrdinaryProtectedPreparationFeasibleThreshold):OrdinaryProtectedPreparation :=by
  exact ordinary_preparation_from_feasible (ordinary_preparation_feasible_from_abundance_threshold hfeasible)
end Oberwolfach
