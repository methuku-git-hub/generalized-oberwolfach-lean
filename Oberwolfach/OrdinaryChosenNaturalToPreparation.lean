module

public import Oberwolfach.OrdinaryNaturalToPreparation

@[expose] public section
/-! It suffices to choose one suitable common reserved component family
before sampling; no universal choice of that family is needed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryChosenNaturalPreparationProbability : Prop :=
  ∀(θ α₀ εmax ρstar β:ℝ),
    (1/2:ℝ)≤θ→θ<1→0<α₀→0<εmax→∀(hρstar:0<ρstar),ρstar≤1→0<β→β≤1→
  ∀rstar:ℕ,3≤rstar→
  ∃ξ:ℝ,0<ξ ∧ ∀χ:ℝ,0<χ→χ<1→∃B N:ℕ,1≤B ∧ 1≤N ∧
  ∀n≥N,∀(P:SimpleGraph (Fin n)) (D q:ℕ),
    P.IsRegularOfDegree D→Even D→(θ+α₀)*(n:ℝ)≤D→
  let ρ:ℝ:=2*(q:ℝ)/(D:ℝ);
  ∀(hρlo:ρstar≤ρ) (hρhi:ρ≤1),∀F:Fin q→SimpleGraph (Fin n),
    (∀w,(F w).IsRegularOfDegree 2)→
    (∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ)→
    (∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=rstar)).card:ℝ))→
  ∃C:∀u,Finset (F u).ConnectedComponent,
    (∀u (c:↥(C u)),Fintype.card c.val=rstar) ∧
  ∃I:Finset (Fin n),(I.card:ℝ)≤εmax*n ∧
    1-χ-1/(n:ℝ)^10≤
      (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ
        (hρstar.le.trans hρlo) hρhi)).probability
        (fun σ=>OrdinaryNaturalPreparationCertificate (r:=rstar) P (retainedGraph P σ) I ξ B F C)

theorem ordinary_chosen_natural_probability_implies_preparation
    (hNatural:OrdinaryChosenNaturalPreparationProbability):OrdinaryProtectedPreparation :=by
  intro θ α₀ εmax ρstar β hθ hθ1 hα hε hρstar hρstar1 hβ hβ1 r hr
  obtain ⟨ξ,hξ,hNatural⟩:=hNatural θ α₀ εmax ρstar β hθ hθ1 hα hε hρstar hρstar1 hβ hβ1 r hr
  refine ⟨ξ,hξ,?_⟩
  intro χ hχ hχ1
  obtain ⟨B,N,hB,hN,hNatural⟩:=hNatural χ hχ hχ1
  refine ⟨B,N,hB,hN,?_⟩
  intro n hn P D q hP hEven hdegree ρ hρlo hρhi F hF hthreshold habundance
  obtain ⟨C,hsize,I,hI,hprob⟩:=hNatural n hn P D q hP hEven hdegree hρlo hρhi F hF hthreshold habundance
  refine ⟨I,hI,?_⟩
  exact ordinary_natural_certificate_probability _ (fun σ=>retainedGraph P σ) P I ξ B F hF C (by omega) hsize _ hprob
end Oberwolfach
