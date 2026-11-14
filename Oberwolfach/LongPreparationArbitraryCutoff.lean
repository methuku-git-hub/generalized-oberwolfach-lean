module

public import Oberwolfach.LongProtectedPreparationStatement

@[expose] public section
/-! If the long-cycle preparation proposition holds, its cutoff can be
selected above any previously fixed cutoff without changing its other
parameters or its probability estimate. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_arbitrary_cutoff
    (hLong:LongProtectedPreparation) (θ α₀ εmax ρstar:ℝ)
    (hθ:(1/2:ℝ)≤θ) (hθ1:θ<1) (hα:0<α₀) (hε:0<εmax)
    (hρstar:0<ρstar) (hρstar1:ρstar≤1) (KExtra:ℕ):
  ∃K:ℕ,KExtra≤K ∧ 3≤K ∧ ∃ξ:ℝ,0<ξ ∧ ∀χ:ℝ,0<χ→χ<1→∃B N:ℕ,1≤B ∧ 1≤N ∧
  ∀n≥N,∀(P:SimpleGraph (Fin n)) (D q:ℕ),
    P.IsRegularOfDegree D→Even D→(θ+α₀)*(n:ℝ)≤D→
  let ρ:ℝ:=2*(q:ℝ)/(D:ℝ);
  ∀(hρlo:ρstar≤ρ) (hρhi:ρ≤1),
  ∀F:Fin q→SimpleGraph (Fin n),
    (∀w,(F w).IsRegularOfDegree 2)→
    (∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ)→
    (∀w,(n:ℝ)/2≤((Finset.univ.filter (fun v=>K<Fintype.card ((F w).connectedComponentMk v))).card:ℝ))→
  ∃I:Finset (Fin n), (I.card:ℝ)≤εmax*n ∧
    1-χ-1/(n:ℝ)^10≤
      (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ
        (hρstar.le.trans hρlo) hρhi)).probability
        (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F) :=by
  obtain ⟨K₀,hK₀,ξ,hξ,hPrep⟩:=hLong θ α₀ εmax ρstar hθ hθ1 hα hε hρstar hρstar1
  refine ⟨max KExtra K₀,le_max_left _ _,hK₀.trans (le_max_right _ _),ξ,hξ,?_⟩
  intro χ hχ hχ1
  obtain ⟨B,N,hB,hN,hPrep⟩:=hPrep χ hχ hχ1
  refine ⟨B,N,hB,hN,?_⟩
  intro n hn P D q hP hEven hdegree ρ hρlo hρhi F hF hthreshold hlong
  apply hPrep n hn P D q hP hEven hdegree hρlo hρhi F hF hthreshold
  intro w
  apply (hlong w).trans
  have hsubset:(Finset.univ.filter (fun v=>max KExtra K₀<Fintype.card ((F w).connectedComponentMk v)))⊆
      (Finset.univ.filter (fun v=>K₀<Fintype.card ((F w).connectedComponentMk v))):=by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_le_of_lt (le_max_right _ _) (Finset.mem_filter.mp hv).2⟩
  exact_mod_cast Finset.card_le_card hsubset
end Oberwolfach
