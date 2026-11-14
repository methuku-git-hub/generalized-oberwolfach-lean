module

public import Oberwolfach.ProtectedFactorPreparation

@[expose] public section
/-! The manuscript's long-cycle preparation proposition as a proposition;
no proof of it is asserted here. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def LongProtectedPreparation : Prop :=
  ∀(θ α₀ εmax ρstar:ℝ),
    (1/2:ℝ)≤θ→θ<1→0<α₀→0<εmax→∀(hρstar:0<ρstar),ρstar≤1→
  ∃K:ℕ,3≤K ∧ ∃ξ:ℝ,0<ξ ∧ ∀χ:ℝ,0<χ→χ<1→∃B N:ℕ,1≤B ∧ 1≤N ∧
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
        (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F)
end Oberwolfach
