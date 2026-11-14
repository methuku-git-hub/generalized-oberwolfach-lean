module

public import Oberwolfach.OrdinaryFixedVortexCleanupMarginsFromEdit
public import Oberwolfach.OrdinaryVortexCanonicalEditCapSmall
public import Oberwolfach.OrdinaryFixedVortexCleanupDomainGeometry

@[expose] public section
/-! Choose the cleanup tolerance before the cap. If the cap is sufficiently
small relative to both vortex domains, all cleanup and balance inequalities
hold at every level, including the initial level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_canonical_cleanup_margins
    (ε ρ₀ α pmin hmin η:ℝ) (d:ℕ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin) (hη:0<η):
    ∃δ:ℝ,0<δ ∧ δ≤α ∧
    ∀(ζ δcap:ℝ),0<ζ→0≤δcap→δcap≤ζ/2→ζ≤δ→ζ≤δ*(ρ₀/8)→
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→∃v₀:ℕ,1≤v₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (i:ℕ),i<Q.length→
    ∀(pR pH θ εR εH βe βh:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤δ→0≤βh→βh≤δ→
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    0≤L ∧ L≤ζ*I.card ∧ L≤δ*I.card ∧ L≤δ*B.card ∧
    βe*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εR*I.card+
      3*L≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card ∧
    βh*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εH*B.card+
      2*L≤pH^2*B.card ∧
    pR*β*I.card+εR*I.card+2*(εH*B.card)+3*L≤η*I.card:=by
  obtain ⟨δ,hδ,hδα,hmargin⟩:=ordinary_fixed_vortex_cleanup_margins_from_edit ε ρ₀ α pmin hmin η d
    hε hε1 hρ₀ hα hpmin hhmin hη
  refine ⟨δ,hδ,hδα,?_⟩
  intro ζ δcap hζ hδcap hδζ hζδ hζB β hβ hβ1 hβδ
  obtain ⟨vm,hvm,hmargins⟩:=hmargin β hβ hβ1 hβδ
  obtain ⟨vs,hvs,hsmall⟩:=ordinary_vortex_canonical_edit_cap_small ε ρ₀ ζ δcap d
    hε hε1 hρ₀ hζ hδcap hδζ β hβ hβ1
  obtain ⟨vg,hvg,hgeom⟩:=ordinary_fixed_vortex_cleanup_domain_geometry β ε ρ₀ hβ hβ1 hε hε1 hρ₀ 1
  refine ⟨max vm (max vs vg),by omega,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q i hi pR pH θ εR εH βe βh
    hpR hpR1 hpH hθ hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh I B L
  have hs:=hsmall V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i hi
  have hg:=hgeom V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i hi
  have hI0:(0:ℝ)≤I.card:=by positivity
  have hLI:L≤δ*I.card:=hs.2.trans (mul_le_mul_of_nonneg_right hζδ hI0)
  have hLB:L≤δ*B.card:=by
    have h1:=mul_le_mul_of_nonneg_right hζB hI0
    have h2:=mul_le_mul_of_nonneg_left hg.2.2.2.2.1 hδ.le
    nlinarith only [hs.2,h1,h2]
  have hh:=hmargins V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i hi
    pR pH θ εR εH βe βh L hpR hpR1 hpH hθ hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh hs.1 hLI hLB
  exact ⟨hs.1,hs.2,hLI,hLB,hh.1,hh.2.1,hh.2.2⟩
end Oberwolfach
