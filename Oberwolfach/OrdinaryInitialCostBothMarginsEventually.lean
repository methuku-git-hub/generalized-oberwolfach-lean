module

public import Oberwolfach.OrdinaryInitialConflictBudgetEventually
public import Oberwolfach.OrdinaryInitialCostToInner
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! The ambient matching edit fits both the first inner-vertex and inner-hub
margins when the edit rate is selected before the spacing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_cost_both_margins_eventually
    (d:ℕ) (η δ ε ρ₀:ℝ) (hη:0<η) (hδ:0≤δ) (hε:0<ε) (hρ₀:0<ρ₀)
    (hsmall:15*η≤(min δ (δ*(ρ₀/8)))*ε/2):
    ∃N:ℕ,∀{n q D mv:ℕ},N≤n→0<n→∀(P:SimpleGraph (Fin n)) (β:ℝ)
    (Vor:Vortex (Fin q) P D β ε mv),P.IsRegularOfDegree D→(n:ℝ)/2≤D→
    ρ₀ ≤ initialIndexDensity (Fin q) D→initialIndexDensity (Fin q) D≤1→
    0≤β→β≤1/4→0<mv→∀cost:ℝ,0≤cost→cost≤14*η*n→
    cost≤δ*(markedVortexInnerVertices Vor 0).card ∧
    cost≤δ*(markedVortexInnerHubs Vor 0).card ∧
    cost+2*((3*d:ℕ):ℝ)≤δ*(markedVortexInnerVertices Vor 0).card :=by
  obtain ⟨N,hN⟩:=ordinary_initial_conflict_budget_eventually d η hη
  refine ⟨N,?_⟩
  intro n q D mv hn hnpos P β Vor hreg hD hρlo hρhi hβ hβ1 hm cost hcost0 hcost
  let ζ:=min δ (δ*(ρ₀/8))
  have hζ:0≤ζ:=by dsimp [ζ];positivity
  have hscaled:=ordinary_initial_cost_to_inner P D mv β ε Vor hε hm η ζ
    (cost+2*((3*d:ℕ):ℝ)) hζ hsmall (by simpa only [Fintype.card_fin] using hN n hn cost hcost)
  have hI:cost+2*((3*d:ℕ):ℝ)≤δ*(markedVortexInnerVertices Vor 0).card:=
    hscaled.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hJsize: (ρ₀/8)*((markedVortexInnerVertices Vor 0).card:ℝ)≤(markedVortexInnerHubs Vor 0).card:=by
    have hh:=marked_vortex_fixed_ambient_size_fields Vor hreg (by simpa using hnpos) (by simpa using hD)
      hρ₀ hρlo hρhi hβ hβ1 hε hm 0 Vor.length_pos
    exact hh.2.1
  have hJ:cost+2*((3*d:ℕ):ℝ)≤δ*(markedVortexInnerHubs Vor 0).card:=by
    have hh:=hscaled.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
    nlinarith [mul_le_mul_of_nonneg_left hJsize hδ]
  have hL:0≤2*((3*d:ℕ):ℝ):=by positivity
  exact ⟨by linarith,by linarith,hI⟩
end Oberwolfach
