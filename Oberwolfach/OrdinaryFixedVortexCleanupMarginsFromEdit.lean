module

public import Oberwolfach.OrdinaryVortexCleanupUniformOriginalMargins

@[expose] public section
/-! The original vortex means supply all three cleanup and balance margins
uniformly once the actual edit is small on both inner domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_cleanup_margins_from_edit
    (ε ρ₀ α pmin hmin η:ℝ) (d:ℕ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin) (hη:0<η):
    ∃δ:ℝ,0<δ ∧ δ≤α ∧ ∀β:ℝ,0≤β→β≤1/4→β≤δ→
    ∃v₀:ℕ,1≤v₀ ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (i:ℕ),i<Q.length→
    ∀(pR pH θ εR εH βe βh L:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤δ→0≤βh→βh≤δ→
      0≤L→L≤δ*(markedVortexInnerVertices Q i).card→L≤δ*(markedVortexInnerHubs Q i).card→
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    βe*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εR*I.card+
      3*L≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card ∧
    βh*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εH*B.card+
      2*L≤pH^2*B.card ∧
    pR*β*I.card+εR*I.card+2*(εH*B.card)+3*L≤η*I.card:=by
  obtain ⟨δ,hδ,hδα,hmain⟩:=ordinary_vortex_cleanup_uniform_original_margins ε ρ₀ α pmin hmin η (3*d)
    hε hε1 hρ₀ hα hpmin hhmin hη
  refine ⟨δ,hδ,hδα,?_⟩
  intro β hβ hβ1 hβδ
  obtain ⟨v₀,hv₀,hmain⟩:=hmain β hβ hβ1 hβδ
  refine ⟨v₀,hv₀,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q i hi pR pH θ εR εH βe βh L
    hpR hpR1 hpH hθ hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh hL0 hLI hLB I B
  have hh:=hmain V U P D vsize hreg hn hD hρlo hρhi hv Q i hi pR pH θ εR εH βe βh L
    hpR hpR1 hpH hθ hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh hL0 hLI hLB
  have hc:(0:ℝ)≤2*((3*d:ℕ):ℝ):=by positivity
  exact ⟨by linarith [hh.1],by linarith [hh.2.1],by linarith [hh.2.2]⟩
end Oberwolfach
