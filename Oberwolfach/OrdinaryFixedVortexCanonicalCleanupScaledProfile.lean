module

public import Oberwolfach.OrdinaryVortexNormalizedParentBounds
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

theorem ordinary_fixed_vortex_canonical_cleanup_scaled_profile
    (ρ₀ α pmin hmin:ℝ) (d:ℕ) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃cProfile:ℝ,0<cProfile ∧
    ∀ε:ℝ,0<ε→ε<1/4→∀η:ℝ,0<η→∃δ:ℝ,0<δ ∧ δ≤α ∧
    ∀(ζ δcap:ℝ),0<ζ→0≤δcap→δcap≤ζ/2→ζ≤δ→ζ≤δ*(ρ₀/8)→
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→∃v₀:ℕ,1≤v₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (i:ℕ),i<Q.length→
    ∀(pR pH θ εR εH βe βh:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cProfile*ε→0≤βh→βh≤cProfile*ε→
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    0≤L ∧ L≤ζ*I.card ∧ L≤δ*I.card ∧ L≤δ*B.card ∧
    βe*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εR*I.card+
      3*L≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card ∧
    βh*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εH*B.card+
      2*L≤pH^2*B.card ∧
    pR*β*I.card+εR*I.card+2*(εH*B.card)+3*L≤η*I.card :=by
  let μ:ℝ:=pmin^2*hmin*α
  let ν:ℝ:=hmin^2
  let cProfile:ℝ:=min (μ/16) (ν*ρ₀/128)
  have hμ:0<μ:=by dsimp [μ];positivity
  have hν:0<ν:=by dsimp [ν];positivity
  have hc:0<cProfile:=by dsimp [cProfile];positivity
  have hcμ:cProfile≤μ/16:=min_le_left _ _
  have hcν:cProfile≤ν*ρ₀/128:=min_le_right _ _
  refine ⟨cProfile,hc,?_⟩
  intro ε hε hε1 η hη
  obtain ⟨δProfile,hProfile,hProfileα,hprof⟩:=ordinary_fixed_vortex_canonical_cleanup_margins
    ε ρ₀ (α/2) pmin (hmin/2) 1 d hε hε1 hρ₀ (by positivity) hpmin (by positivity) (by norm_num)
  obtain ⟨δBal,hBal,hBalα,hbalance⟩:=ordinary_fixed_vortex_canonical_cleanup_margins
    ε ρ₀ α pmin hmin η d hε hε1 hρ₀ hα hpmin hhmin hη
  let δ:ℝ:=min δProfile δBal
  have hδ:0<δ:=by dsimp [δ];positivity
  have hδp:δ≤δProfile:=min_le_left _ _
  have hδb:δ≤δBal:=min_le_right _ _
  have hδα:δ≤α:=by linarith
  refine ⟨δ,hδ,hδα,?_⟩
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
  have hpmin1:pmin≤1:=hpR.trans hpR1
  have hp:=hprof V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i hi pmin (hmin/2) (1/2) εR εH 0 0
    le_rfl hpmin1 le_rfl (by norm_num) hεR0 (hεR.trans hδp) hεH0 (hεH.trans hδp) (by norm_num) hProfile.le (by norm_num) hProfile.le
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
  have hnorm:=ordinary_vortex_normalized_parent_bounds Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε (by omega) i hi
  have hParent0:(0:ℝ)≤Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):=by positivity
  have hI0:(0:ℝ)≤I.card:=by positivity
  have hB0:(0:ℝ)≤B.card:=by positivity
  have hcard:(Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):ℝ)=
      Fintype.card (markedVortexVertexType Q i)+Fintype.card (markedVortexHubType Q i):=by simp
  have hE1:=mul_le_mul_of_nonneg_right hβe hParent0
  have hH1:=mul_le_mul_of_nonneg_right hβh hParent0
  have hE2:=mul_le_mul_of_nonneg_left hnorm.1 hc.le
  have hH2:=mul_le_mul_of_nonneg_left hnorm.2 hc.le
  have hE3:=mul_le_mul_of_nonneg_right hcμ hI0
  have hH3:=mul_le_mul_of_nonneg_right hcν hB0
  rw [hcard] at hE1 hH1
  have hExtraE:βe*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)≤(μ/4)*I.card:=by
    rw [hcard]
    nlinarith only [hE1,hE2,hE3]
  have hExtraH:βh*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)≤(ν/4)*B.card:=by
    rw [hcard]
    nlinarith only [hH1,hH2,hH3,hρ₀]
  have hβsmall:β≤α/2:=hβδ.trans (hδp.trans hProfileα)
  have hRhsE:pmin^2*(hmin/2)*(2*((1/2:ℝ)+α/2-β/2)-1)*I.card≤(μ/2)*I.card:=by
    have hh:0≤pmin^2*(hmin/2)*I.card:=by positivity
    dsimp [μ]
    nlinarith only [hβ,hh]
  have hBaseE:εR*I.card+3*L≤(μ/2)*I.card:=by
    have hh:=hp.2.2.2.2.1
    nlinarith only [hh,hRhsE]
  have hBaseH:εH*B.card+2*L≤(ν/4)*B.card:=by
    have hh:=hp.2.2.2.2.2.1
    dsimp [ν]
    nlinarith only [hh]
  have hpR0:0≤pR:=hpmin.le.trans hpR
  have hpH0:0≤pH:=hhmin.le.trans hpH
  have hpRsq:pmin^2≤pR^2:=by nlinarith [sq_nonneg (pR-pmin)]
  have hpHsq:hmin^2≤pH^2:=by nlinarith [sq_nonneg (pH-hmin)]
  have hprod:pmin^2*hmin≤pR^2*pH:=by
    calc
      pmin^2*hmin≤pR^2*hmin:=mul_le_mul_of_nonneg_right hpRsq hhmin.le
      _≤pR^2*pH:=mul_le_mul_of_nonneg_left hpH (sq_nonneg pR)
  have hcoeff:α≤2*(θ+α-β/2)-1:=by linarith
  have hTargetE:μ*I.card≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card:=by
    have h1:=mul_le_mul_of_nonneg_right hprod (mul_nonneg hα.le hI0)
    have h2:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (mul_nonneg (sq_nonneg pR) hpH0) hI0)
    dsimp [μ]
    nlinarith only [h1,h2]
  have hTargetH:ν*B.card≤pH^2*B.card:=by
    dsimp [ν];exact mul_le_mul_of_nonneg_right hpHsq hB0
  refine ⟨hp.1,hp.2.1,hLI,hLB,?_,?_,hb.2.2.2.2.2.2⟩
  · nlinarith only [hExtraE,hBaseE,hTargetE,hμ,hI0]
  · nlinarith only [hExtraH,hBaseH,hTargetH,hν,hB0]
end Oberwolfach
