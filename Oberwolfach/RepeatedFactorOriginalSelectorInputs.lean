module

public import Oberwolfach.RepeatedFactorSelectorDensityInputs
public import Oberwolfach.RepeatedFactorSingleClassInputs
public import Oberwolfach.LongRegularHostNumericInputs

@[expose] public section
/-! Supply the actual regular-host, repeated-family and one-class density
inputs to the selector from the original long-class hypotheses. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem repeated_factor_original_selector_inputs
    {n D K:ℕ} (hn:0<n) (P F₀:SimpleGraph (Fin n))
    (hreg:P.IsRegularOfDegree D) (hEven:Even D) (hF₀:F₀.IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:Allowed.Nonempty) (hvalid:∀r∈Allowed,3≤r)
    (hFAllowed:AllowedCycleLengths F₀ Allowed) (hLong:factorPreparationClass F₀ K=none)
    (αRef ρ₀ θ:ℝ) (hα:0<αRef) (hρ₀:0<ρ₀) (hρone:ρ₀≤1)
    (hmin:(allowedThreshold Allowed+2*αRef)*n≤(D:ℝ)) (r:ℕ):
    let U:=Fin (D/2)
    let F:U→SimpleGraph (Fin n):=fun _=>F₀
    let ρ:=initialIndexDensity U D
    let density:Unit→ℝ:=fun _=>1
    let kstar:=ρ₀/(800*((r+4:ℕ):ℝ));
    0<D ∧ (n:ℝ)/2≤D ∧ (D:ℝ)≤2*n ∧ Fintype.card U≤n ∧
    (∀u,AllowedCycleLengths (F u) Allowed) ∧ (∀u,factorPreparationClass (F u) K=none) ∧
    ρ₀≤ρ ∧ ρ≤1 ∧ kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/((r+4:ℕ):ℝ))/2 ∧
    (∀j,0≤density j) ∧ (∑j,density j)=1 ∧
    (∀j,density j=0 ∨ 1≤density j) ∧ 1≤density () ∧ ρ=density () :=by
  intro U F ρ density kstar
  have hnumer:=long_regular_host_numeric_inputs n D hn U Allowed hAllowed hvalid (2*αRef) (by positivity) P hreg hmin
  obtain ⟨hD,hDlo,hDhi,_,_,_⟩:=hnumer
  have hDle:D≤n:=by simpa using regular_degree_le_card hreg (by simpa using hn)
  have hU:Fintype.card U≤n:=by dsimp [U]; simp only [Fintype.card_fin]; omega
  have hdens:=repeated_factor_selector_density_inputs (K:=K) F₀ hF₀ r θ ρ₀ hρ₀ hρone hD hEven
  have hsingle:=repeated_factor_single_class_inputs D hD hEven
  dsimp only [] at hdens hsingle
  obtain ⟨hρlo,hρhi,hk₁,hk₂⟩:=hdens
  obtain ⟨hNonneg,hSum,hParts,hClass,hEq⟩:=hsingle
  exact ⟨hD,hDlo,hDhi,hU,(fun _=>hFAllowed),(fun _=>hLong),hρlo,hρhi,hk₁,hk₂,hNonneg,hSum,hParts,hClass,hEq⟩
end Oberwolfach
