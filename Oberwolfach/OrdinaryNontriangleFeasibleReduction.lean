module

public import Oberwolfach.OrdinaryTriangleNontrianglePreparationReduction

@[expose] public section
/-! The threshold-feasible nontriangle case suffices for the original
nontriangle statement: abundance rules out the complementary branch. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryNontriangleFeasibleProtectedPreparation : Prop :=
  ∀(θ α₀ εmax ρstar β:ℝ),
    (1/2:ℝ)≤θ→θ<1→0<α₀→0<εmax→∀(hρstar:0<ρstar),ρstar≤1→0<β→β≤1→
  ∀rstar:ℕ,4≤rstar→cycleThreshold rstar≤θ→
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

theorem ordinary_nontriangle_feasible_reduction
    (hFeasible:OrdinaryNontriangleFeasibleProtectedPreparation):OrdinaryNontriangleProtectedPreparation :=by
  intro θ α₀ εmax ρstar β hθ hθ1 hα hε hρ hρ1 hβ hβ1 rstar hr
  by_cases hcycle:cycleThreshold rstar≤θ
  · exact hFeasible θ α₀ εmax ρstar β hθ hθ1 hα hε hρ hρ1 hβ hβ1 rstar hr hcycle
  · refine ⟨1,by norm_num,?_⟩
    intro χ hχ hχ1
    refine ⟨1,2,by omega,by omega,?_⟩
    intro n hn P D q hreg hEven hdegree ρ hρlo hρhi F hF hthreshold habundance
    have hρlo':ρstar≤2*(q:ℝ)/(D:ℝ):=by simpa [ρ] using hρlo
    exact False.elim (hcycle (ordinary_abundance_threshold_from_original θ ρstar β hρ hβ
      n D q rstar (by omega) hρlo' F hthreshold habundance))
end Oberwolfach
