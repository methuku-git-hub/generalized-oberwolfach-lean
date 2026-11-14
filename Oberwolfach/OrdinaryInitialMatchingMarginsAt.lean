module

public import Oberwolfach.OrdinaryInitialMatchingEditMarginsBeforeSpacing

@[expose] public section
/-! Name the first-level margins so they can be carried through the ordered
certificate and same-sample construction without expanding the callback. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryInitialMatchingMarginsAt
    (ρ₀ α pmin hmin ε bal cBoundary δ η β:ℝ) (d m₀ N:ℕ):Prop :=
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
    (initialIndexDensity (Fin q) D*pH)*β*I.card+εR*I.card+2*(εH*J.card)+3*L≤bal*I.card

theorem ordinary_initial_matching_edit_margins_named_before_spacing
    (ρ₀ α pmin hmin:ℝ) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃cBoundary:ℝ,0<cBoundary ∧ ∀ε:ℝ,0<ε→ε<1/4→∀bal:ℝ,0<bal→
    ∃δ η:ℝ,0<δ ∧ δ≤α ∧ δ≤bal ∧ 0<η ∧
    ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δ→∃m₀ N:ℕ,1≤m₀ ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε bal cBoundary δ η β d m₀ N :=by
  obtain ⟨c,hc,hmain⟩:=ordinary_initial_matching_edit_margins_before_spacing ρ₀ α pmin hmin hρ₀ hα hpmin hhmin
  refine ⟨c,hc,?_⟩
  intro ε hε hε1 bal hbal
  obtain ⟨δ,η,hδ,hδα,hδbal,hη,hmain⟩:=hmain ε hε hε1 bal hbal
  refine ⟨δ,η,hδ,hδα,hδbal,hη,?_⟩
  intro d β hβ hβ1 hβδ
  obtain ⟨m₀,N,hm₀,hmain⟩:=hmain d β hβ hβ1 hβδ
  exact ⟨m₀,N,hm₀,hmain⟩
end Oberwolfach
