module

public import Oberwolfach.OrdinaryVortexCleanupSeparatedLinearBoundaryMarginsExplicitBeforeSpacing

@[expose] public section
/-! Before sampling, the original vortex geometry supplies the three
initial-correction margins while retaining linear boundary tolerances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_initial_separated_margins_before_spacing
    (ρ₀ α pmin hmin:ℝ) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃cBoundary:ℝ,0<cBoundary ∧ ∀ε:ℝ,0<ε→ε<1/4→∀η:ℝ,0<η→
    ∃δ:ℝ,0<δ ∧ δ≤α ∧ δ≤η ∧ ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δ→
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (i:ℕ),i<Q.length→
    ∀(pR pH θ εR εH βe βh:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
      pR=initialIndexDensity U D*pH→
    let I:=markedVortexInnerVertices Q i;let J:=markedVortexInnerHubs Q i;
    let L:=2*((3*d:ℕ):ℝ);
    βe*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εR*I.card+
      3*L≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card ∧
    βh*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εH*J.card+
      2*L≤pH^2*J.card ∧
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*J.card)+3*L≤η*I.card:=by
  obtain ⟨c,hc,hmain⟩:=ordinary_vortex_cleanup_separated_linear_boundary_margins_explicit_before_spacing
    ρ₀ α pmin hmin hρ₀ hα hpmin hhmin
  refine ⟨c,hc,?_⟩
  intro ε hε hε1 η hη
  obtain ⟨δ,hδ,hδα,hδη,hδmain⟩:=hmain ε hε hε1 η hη
  refine ⟨δ,hδ,hδα,hδη,?_⟩
  intro d β hβ hβ1 hβδ
  obtain ⟨m₀,hm₀,hm⟩:=hδmain (3*d) β hβ hβ1 hβδ
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hmm Q i hi pR pH θ εR εH βe βh
    hpR hpR1 hpH hθ hεR hεRδ hεH hεHδ hβe hβec hβh hβhc hpEq I J L
  have hh:=hm V U P D m hreg hn hD hρlo hρhi hmm Q i hi pR pH θ εR εH βe βh 0
    hpR hpR1 hpH hθ hεR hεRδ hεH hεHδ hβe hβec hβh hβhc (by norm_num) (by positivity) (by positivity)
  dsimp only at hh
  simp only [add_zero] at hh
  rw [←hpEq]
  exact hh
end Oberwolfach
