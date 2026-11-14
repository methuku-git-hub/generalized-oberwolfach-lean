module

public import Oberwolfach.OrdinaryVortexCleanupSeparatedLinearBoundaryMarginsExplicitBeforeSpacing
public import Oberwolfach.OrdinaryInitialCostBothMarginsEventually

@[expose] public section
/-! Choose a matching-edit rate before spacing so that the actual initial
remainder satisfies all three separated profile margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_matching_edit_margins_before_spacing
    (ρ₀ α pmin hmin:ℝ) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃cBoundary:ℝ,0<cBoundary ∧ ∀ε:ℝ,0<ε→ε<1/4→∀bal:ℝ,0<bal→
    ∃δ η:ℝ,0<δ ∧ δ≤α ∧ δ≤bal ∧ 0<η ∧
    ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δ→∃m₀ N:ℕ,1≤m₀ ∧
    ∀{n q D m:ℕ},N≤n→0<n→m₀≤m→∀(P:SimpleGraph (Fin n)) (Q:Vortex (Fin q) P D β ε m),
    P.IsRegularOfDegree D→(n:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity (Fin q) D→initialIndexDensity (Fin q) D≤1→
    ∀(pR pH θ εR εH βe βh cost:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
      pR=initialIndexDensity (Fin q) D*pH→0≤cost→cost≤14*η*n→
    let I:=markedVortexInnerVertices Q 0;let J:=markedVortexInnerHubs Q 0;
    let L:=cost+2*((3*d:ℕ):ℝ);
    βe*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0)+εR*I.card+
      3*L≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card ∧
    βh*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0)+εH*J.card+
      2*L≤pH^2*J.card ∧
    (initialIndexDensity (Fin q) D*pH)*β*I.card+εR*I.card+2*(εH*J.card)+3*L≤bal*I.card :=by
  obtain ⟨c,hc,hmain⟩:=ordinary_vortex_cleanup_separated_linear_boundary_margins_explicit_before_spacing
    ρ₀ α pmin hmin hρ₀ hα hpmin hhmin
  refine ⟨c,hc,?_⟩
  intro ε hε hε1 bal hbal
  obtain ⟨δ,hδ,hδα,hδbal,hmain⟩:=hmain ε hε hε1 bal hbal
  let η:ℝ:=min δ (δ*(ρ₀/8))*ε/120
  have hη:0<η:=by dsimp [η];positivity
  have hsmall:15*η≤min δ (δ*(ρ₀/8))*ε/2:=by
    dsimp [η]
    have hh:0≤min δ (δ*(ρ₀/8))*ε:=by positivity
    linarith
  refine ⟨δ,η,hδ,hδα,hδbal,hη,?_⟩
  intro d β hβ hβ1 hβδ
  obtain ⟨m₀,hm₀,hmargin⟩:=hmain (3*d) β hβ hβ1 hβδ
  obtain ⟨N,hN⟩:=ordinary_initial_cost_both_margins_eventually d η δ ε ρ₀ hη hδ.le hε hρ₀ hsmall
  refine ⟨m₀,N,hm₀,?_⟩
  intro n q D m hn hnpos hm P Q hreg hD hρlo hρhi pR pH θ εR εH βe βh cost
    hpR hpR1 hpH hθ hεR hεRδ hεH hεHδ hβe hβec hβh hβhc hpEq hcost0 hcost I J L
  have hcosts:=hN hn hnpos P β Q hreg hD hρlo hρhi hβ hβ1 (by omega) cost hcost0 hcost
  have h:=hmargin (Fin n) (Fin q) P D m hreg (by simpa using hnpos) (by simpa using hD) hρlo hρhi hm Q 0 Q.length_pos
    pR pH θ εR εH βe βh cost hpR hpR1 hpH hθ hεR hεRδ hεH hεHδ hβe hβec hβh hβhc hcost0 hcosts.1 hcosts.2.1
  dsimp only at h
  rw [←hpEq]
  dsimp only [I,J,L]
  constructor
  · nlinarith only [h.1]
  · constructor
    · nlinarith only [h.2.1]
    · nlinarith only [h.2.2]
end Oberwolfach
