module

public import Oberwolfach.OrdinaryFixedVortexCanonicalCleanupMargins
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

theorem ordinary_fixed_vortex_canonical_cleanup_separated_profile
    (ε ρ₀ α pmin hmin:ℝ) (d:ℕ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃δProfile:ℝ,0<δProfile ∧ δProfile≤α ∧
    ∀η:ℝ,0<η→∃δ:ℝ,0<δ ∧ δ≤δProfile ∧
    ∀(ζ δcap:ℝ),0<ζ→0≤δcap→δcap≤ζ/2→ζ≤δ→ζ≤δ*(ρ₀/8)→
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→∃v₀:ℕ,1≤v₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (i:ℕ),i<Q.length→
    ∀(pR pH θ εR εH βe βh:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤δProfile→0≤βh→βh≤δProfile→
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    0≤L ∧ L≤ζ*I.card ∧ L≤δ*I.card ∧ L≤δ*B.card ∧
    βe*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εR*I.card+
      3*L≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card ∧
    βh*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εH*B.card+
      2*L≤pH^2*B.card ∧
    pR*β*I.card+εR*I.card+2*(εH*B.card)+3*L≤η*I.card :=by
  obtain ⟨δProfile,hProfile,hProfileα,hprof⟩:=ordinary_fixed_vortex_canonical_cleanup_margins
    ε ρ₀ α pmin hmin 1 d hε hε1 hρ₀ hα hpmin hhmin (by norm_num)
  refine ⟨δProfile,hProfile,hProfileα,?_⟩
  intro η hη
  obtain ⟨δBal,hBal,hBalα,hbalance⟩:=ordinary_fixed_vortex_canonical_cleanup_margins
    ε ρ₀ α pmin hmin η d hε hε1 hρ₀ hα hpmin hhmin hη
  let δ:ℝ:=min δProfile δBal
  have hδ:0<δ:=by dsimp [δ];positivity
  have hδp:δ≤δProfile:=min_le_left _ _
  have hδb:δ≤δBal:=min_le_right _ _
  refine ⟨δ,hδ,hδp,?_⟩
  intro ζ δcap hζ hδcap0 hδcapζ hζδ hζB β hβ hβ1 hβδ
  have hρnonneg:0≤ρ₀/8:=by positivity
  have hζp:ζ≤δProfile:=hζδ.trans hδp
  have hζb:ζ≤δBal:=hζδ.trans hδb
  have hζBp:ζ≤δProfile*(ρ₀/8):=hζB.trans (mul_le_mul_of_nonneg_right hδp hρnonneg)
  have hζBb:ζ≤δBal*(ρ₀/8):=hζB.trans (mul_le_mul_of_nonneg_right hδb hρnonneg)
  obtain ⟨vp,hvp,hprof⟩:=hprof ζ δcap hζ hδcap0 hδcapζ hζp hζBp β hβ hβ1 (hβδ.trans hδp)
  obtain ⟨vb,hvb,hbalance⟩:=hbalance ζ δcap hζ hδcap0 hδcapζ hζb hζBb β hβ hβ1 (hβδ.trans hδb)
  refine ⟨max vp vb,by omega,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q i hi pR pH θ εR εH βe βh
    hpR hpR1 hpH hθ hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh I B L
  have hp:=hprof V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i hi pR pH θ εR εH βe βh
    hpR hpR1 hpH hθ hεR0 (hεR.trans hδp) hεH0 (hεH.trans hδp) hβe0 hβe hβh0 hβh
  have hb:=hbalance V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i hi pR pH θ εR εH 0 0
    hpR hpR1 hpH hθ hεR0 (hεR.trans hδb) hεH0 (hεH.trans hδb) (by norm_num) hBal.le (by norm_num) hBal.le
  have hLI:L≤δ*I.card:=by
    rcases le_total δProfile δBal with h | h
    · have heq:δ=δProfile:=min_eq_left h
      rw [heq];exact hp.2.2.1
    · have heq:δ=δBal:=min_eq_right h
      rw [heq];exact hb.2.2.1
  have hLB:L≤δ*B.card:=by
    rcases le_total δProfile δBal with h | h
    · have heq:δ=δProfile:=min_eq_left h
      rw [heq];exact hp.2.2.2.1
    · have heq:δ=δBal:=min_eq_right h
      rw [heq];exact hb.2.2.2.1
  exact ⟨hp.1,hp.2.1,hLI,hLB,hp.2.2.2.2.1,hp.2.2.2.2.2.1,hb.2.2.2.2.2.2⟩
end Oberwolfach
