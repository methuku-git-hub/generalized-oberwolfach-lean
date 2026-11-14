module

public import Oberwolfach.OrdinaryTriangleFeasiblePreparationOptimized
public import Oberwolfach.OrdinaryAbundanceThresholdFromOriginal

@[expose] public section
/-! Remove the feasible-branch test by using the original abundance and
cycle-threshold assumptions in the complementary case. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_preparation_from_original
    (θ α₀ εmax ρ₀ βfreq:ℝ)
    (hθhalf:1/2≤θ) (hθ1:θ<1)
    (hα₀:0<α₀) (hεmax:0<εmax) (hρ₀:0<ρ₀) (hρ₀1:ρ₀≤1)
    (hβfreq:0<βfreq) (hβfreq1:βfreq≤1):
    ∃ξ:ℝ,0<ξ ∧ ∀χ:ℝ,0<χ→χ<1→∃B N:ℕ,1≤B ∧ 1≤N ∧
    ∀n≥N,∀(P:SimpleGraph (Fin n)) (D q:ℕ),
      P.IsRegularOfDegree D→Even D→(θ+α₀)*(n:ℝ)≤D→
    let ρ:ℝ:=2*(q:ℝ)/(D:ℝ);
    ∀(hρlo:ρ₀≤ρ) (hρhi:ρ≤1),∀F:Fin q→SimpleGraph (Fin n),
      (∀u,(F u).IsRegularOfDegree 2)→
      (∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θ)→
      (∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=3)).card:ℝ))→
    ∃I:Finset (Fin n),(I.card:ℝ)≤εmax*n ∧
      1-χ-1/(n:ℝ)^10≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ
        (hρ₀.le.trans hρlo) hρhi)).probability
        (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F)
 :=by
  by_cases hθcycle:cycleThreshold 3≤θ
  · exact ordinary_triangle_feasible_preparation_optimized θ α₀ εmax ρ₀ βfreq hθhalf hθcycle hθ1 hα₀ hεmax hρ₀ hρ₀1 hβfreq hβfreq1
  · refine ⟨1,by norm_num,?_⟩
    intro χ hχ hχ1
    refine ⟨1,2,by omega,by omega,?_⟩
    intro n hn P D q hreg hEven hdegree ρ hρlo hρhi F hF hthreshold habundance
    have hρlo':ρ₀≤2*(q:ℝ)/(D:ℝ):=by simpa [ρ] using hρlo
    exact False.elim (hθcycle (ordinary_abundance_threshold_from_original θ ρ₀ βfreq hρ₀ hβfreq
      n D q 3 (by omega) hρlo' F hthreshold habundance))
end Oberwolfach
