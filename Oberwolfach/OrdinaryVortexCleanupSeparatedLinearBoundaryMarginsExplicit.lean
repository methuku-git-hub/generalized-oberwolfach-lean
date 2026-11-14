module

public import Oberwolfach.OrdinaryCleanupSeparatedMargins
public import Oberwolfach.OrdinaryVortexCleanupUniformMargins
public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! The fixed vortex itself supplies the domain-size ratios and minimum sizes
needed by the uniform cleanup margins. Only the latest trace loss remains to
be bounded on the two inner domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_cleanup_separated_linear_boundary_margins_explicit
    (ρ₀ α pmin hmin:ℝ) (b:ℕ) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃cBoundary:ℝ,0<cBoundary ∧ ∀ε:ℝ,0<ε→ε<1/4→∀η:ℝ,0<η→
    ∃δ:ℝ,0<δ ∧ δ≤α ∧ δ≤η ∧ ∀β:ℝ,0≤β→β≤1/4→β≤δ→
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (i:ℕ),i<Q.length→
    ∀(pR pH θ εR εH βe βh cost:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
      0≤cost→cost≤δ*(markedVortexInnerVertices Q i).card→cost≤δ*(markedVortexInnerHubs Q i).card→
    let I:=markedVortexInnerVertices Q i;let J:=markedVortexInnerHubs Q i;
    βe*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εR*I.card+
      3*(2*(b:ℝ)+cost)≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card ∧
    βh*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εH*J.card+
      2*(2*(b:ℝ)+cost)≤pH^2*J.card ∧
    pR*β*I.card+εR*I.card+2*(εH*J.card)+3*(2*(b:ℝ)+cost)≤η*I.card:=by
  let μ:ℝ:=pmin^2*hmin*α
  let ν:ℝ:=hmin^2
  have hμ:0<μ:=by dsimp [μ];positivity
  have hν:0<ν:=by dsimp [ν];positivity
  let C₀:ℝ:=9+32/ρ₀
  have hC₀:0<C₀:=by dsimp [C₀];positivity
  let cBoundary:ℝ:=min μ ν/(80*C₀)
  have hcBoundary:0<cBoundary:=by dsimp [cBoundary];positivity
  refine ⟨cBoundary,hcBoundary,?_⟩
  intro ε hε hε1 η hη
  let K₀:ℝ:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))
  let K:ℝ:=2*(K₀+1)
  have hK₀:1≤K₀:=by
    dsimp [K₀]
    have h1:0≤1/(ε/2):=by positivity
    have h2:0≤1/((ε/2)*(ρ₀/8)):=by positivity
    linarith
  have hK:1≤K:=by dsimp [K];linarith
  have heq1:ε*(1/(ε/2))=2:=by field_simp
  have heq2:ε*(1/((ε/2)*(ρ₀/8)))=16/ρ₀:=by field_simp <;> norm_num
  have hKexact:ε*(K+1)=5*ε+4+32/ρ₀:=by
    calc
      ε*(K+1)=5*ε+2*(ε*(1/(ε/2)))+2*(ε*(1/((ε/2)*(ρ₀/8)))):=by dsimp [K,K₀];ring
      _=5*ε+4+32/ρ₀:=by rw [heq1,heq2];ring
  have hKbound:ε*(K+1)≤C₀:=by
    rw [hKexact]
    dsimp [C₀]
    linarith
  have hcoef:cBoundary*ε≤min μ ν/(40*(K+1)):=by
    apply (le_div_iff₀ (by positivity:0<40*(K+1))).2
    have hm:=mul_le_mul_of_nonneg_left hKbound (show 0≤40*cBoundary by positivity)
    have heq:cBoundary*40*C₀=min μ ν/2:=by dsimp [cBoundary];field_simp;ring
    have hmin:0≤min μ ν:=le_min hμ.le hν.le
    nlinarith only [hm,heq,hmin]
  obtain ⟨hboundary,hsmall,M,hmargin⟩:=ordinary_cleanup_separated_margins K μ ν η b hK hμ hν hη (by positivity)
  let δ₀:ℝ:=min μ (min ν η)/(40*(K+1))
  let δ:=min δ₀ α
  have hδ:0<δ:=lt_min hsmall hα
  have hδη:δ≤η:=by
    have hmin:min μ (min ν η)≤η:=(min_le_right _ _).trans (min_le_right _ _)
    have hden:1≤40*(K+1):=by linarith [hK]
    have hm:=mul_le_mul_of_nonneg_left hden hη.le
    have hδ₀η:δ₀≤η:=by
      dsimp [δ₀]
      apply (div_le_iff₀ (by positivity:0<40*(K+1))).mpr
      nlinarith only [hmin,hm]
    exact (min_le_left _ _).trans hδ₀η
  refine ⟨δ,hδ,min_le_right _ _,hδη,?_⟩
  intro β hβ0 hβ1 hβ
  obtain ⟨m₀,hm₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ0 hβ1 hε hε1 hρ₀ M
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q i hi pR pH θ εR εH βe βh cost hpRlo hpR1 hpHlo hθ
    hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh hcost0 hcostI hcostJ I J
  have hδle:δ≤δ₀:=min_le_left _ _
  have hh:=hsize V U P D m hreg hn hD hρlo hρhi hm Q i hi
  let A:ℝ:=I.card
  let B:ℝ:=J.card
  let Aparent:ℝ:=Fintype.card (markedVortexVertexType Q i)
  let Bparent:ℝ:=Fintype.card (markedVortexHubType Q i)
  have hA0:0≤A:=by positivity
  have hB0:0≤B:=by positivity
  have hAp0:0≤Aparent:=by positivity
  have hBp0:0≤Bparent:=by positivity
  have hIle:A≤Aparent:=by
    dsimp [A,Aparent]
    exact_mod_cast (Finset.card_le_univ I)
  have hJle:B≤Bparent:=by
    dsimp [B,Bparent]
    exact_mod_cast (Finset.card_le_univ J)
  have hA:(M:ℝ)≤A:=by
    have he:0≤ε*A:=mul_nonneg hε.le hA0
    have h:=hh.2.1
    change (M:ℝ)≤(1-ε)*A at h
    nlinarith only [h,he]
  have hB:(M:ℝ)≤B:=by
    have he:0≤ε*B:=mul_nonneg hε.le hB0
    have h:=hh.2.2.1
    change (M:ℝ)≤(1-ε)*B at h
    nlinarith only [h,he]
  have hU:Bparent≤Aparent:=by
    have hv:0<m:=by omega
    have hu: Fintype.card (markedVortexHubType Q i)≤Fintype.card (markedVortexVertexType Q i):=
      (marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ₀ hρlo hρhi hβ0 hβ1 hε hv i hi).2.2
    dsimp [Aparent,Bparent]
    exact_mod_cast hu
  have hpA:Aparent+Bparent≤K*A:=by
    have h1:Aparent≤K₀*A:=hh.2.2.2.1
    have h2:Bparent≤K₀*A:=hh.2.2.2.2.1
    have hk:(2*K₀:ℝ)≤K:=by dsimp [K];linarith
    have hm:=mul_le_mul_of_nonneg_right hk hA0
    nlinarith only [h1,h2,hm]
  have hpB:Aparent+Bparent≤K*B:=by
    have h1:Aparent≤K₀*B:=hh.2.2.2.2.2
    have hk:(2*K₀:ℝ)≤K:=by dsimp [K];linarith
    have hm:=mul_le_mul_of_nonneg_right hk hB0
    nlinarith only [h1,hU,hm]
  have hBA:B≤K*A:=by
    have h1:Aparent≤K₀*A:=hh.2.2.2.1
    have hk:K₀≤K:=by dsimp [K];linarith
    exact hJle.trans (hU.trans (h1.trans (mul_le_mul_of_nonneg_right hk hA0)))
  have hcostI':cost≤δ₀*A:=hcostI.trans (mul_le_mul_of_nonneg_right hδle hA0)
  have hcostJ':cost≤δ₀*B:=hcostJ.trans (mul_le_mul_of_nonneg_right hδle hB0)
  have hmain:=hmargin A B (Aparent+Bparent) hA hB (add_nonneg hAp0 hBp0) hpA hpB hBA
    β εR εH βe βh cost 1 hβ0 (hβ.trans hδle) hεR0 (hεR.trans hδle) hεH0 (hεH.trans hδle)
    hβe0 (hβe.trans hcoef) hβh0 (hβh.trans hcoef) hcost0 hcostI' hcostJ' (by norm_num) (by norm_num)
  have hγ:α≤2*(θ+α-β/2)-1:=by have ha:=hβ.trans (min_le_right δ₀ α);linarith
  have hpR:0≤pR:=le_trans hpmin.le hpRlo
  have hpH:0≤pH:=le_trans hhmin.le hpHlo
  have hpRsq:pmin^2≤pR^2:=by nlinarith [sq_nonneg (pR-pmin)]
  have hpHsq:hmin^2≤pH^2:=by nlinarith [sq_nonneg (pH-hmin)]
  have hproduct:pmin^2*hmin≤pR^2*pH:=by
    calc
      pmin^2*hmin≤pR^2*hmin:=mul_le_mul_of_nonneg_right hpRsq hhmin.le
      _≤pR^2*pH:=mul_le_mul_of_nonneg_left hpHlo (sq_nonneg pR)
  have hμle:(pmin^2*hmin*α)*A≤pR^2*pH*(2*(θ+α-β/2)-1)*A:=by
    have hh':=mul_le_mul_of_nonneg_right hγ (mul_nonneg (mul_nonneg (sq_nonneg pR) hpH) hA0)
    have hh'':=mul_le_mul_of_nonneg_right hproduct (mul_nonneg hα.le hA0)
    nlinarith only [hh',hh'']
  have hνle:(hmin^2)*B≤pH^2*B:=mul_le_mul_of_nonneg_right hpHsq hB0
  have hpβ:pR*β*A≤1*β*A:=by
    have hh':=mul_le_mul_of_nonneg_right hpR1 (mul_nonneg hβ0 hA0)
    nlinarith only [hh']
  have hcard:(Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):ℝ)=Aparent+Bparent:=by
    simp only [Fintype.card_sum,Nat.cast_add,Aparent,Bparent]
  rw [hcard]
  refine ⟨hmain.1.trans hμle,hmain.2.1.trans hνle,?_⟩
  linarith only [hmain.2.2,hpβ]
end Oberwolfach
