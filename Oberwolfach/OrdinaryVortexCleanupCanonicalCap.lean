module

public import Oberwolfach.OrdinaryVortexCleanupUniformOriginalMargins

@[expose] public section
/-! A cap chosen from the fixed vortex domains, before the random sample,
is small enough for both adaptive hub weights and cleanup margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_cleanup_canonical_cap
    (ε ρ₀ α pmin hmin η ζ:ℝ) (d:ℕ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin) (hη:0<η) (hζ:0<ζ):
    ∃δ:ℝ,0<δ ∧ δ≤α ∧ δ≤ζ/2 ∧ ∀β:ℝ,0≤β→β≤1/4→β≤δ→
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (i:ℕ),i<Q.length→
    ∀(pR pH θ εR εH βe βh:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤δ→0≤βh→βh≤δ→
    let I:=markedVortexInnerVertices Q i;let J:=markedVortexInnerHubs Q i;
    let c:=δ*min (I.card:ℝ) J.card;
    let L:=2*((3*d:ℕ):ℝ)+c;
    0≤c ∧ c≤δ*I.card ∧ c≤δ*J.card ∧ 0≤L ∧ L≤ζ*I.card ∧
    βe*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εR*I.card+
      3*L≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card ∧
    βh*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εH*J.card+
      2*L≤pH^2*J.card ∧
    pR*β*I.card+εR*I.card+2*(εH*J.card)+3*L≤η*I.card := by
  obtain ⟨δm,hδm,hδmα,hmargin⟩:=ordinary_vortex_cleanup_uniform_original_margins ε ρ₀ α pmin hmin η (3*d)
    hε hε1 hρ₀ hα hpmin hhmin hη
  let δ:=min δm (ζ/2)
  have hδ:0<δ:=lt_min hδm (by positivity)
  have hδm':δ≤δm:=min_le_left _ _
  have hδζ:δ≤ζ/2:=min_le_right _ _
  refine ⟨δ,hδ,hδm'.trans hδmα,hδζ,?_⟩
  intro β hβ hβ1 hβδ
  obtain ⟨mm,hmm,hmain⟩:=hmargin β hβ hβ1 (hβδ.trans hδm')
  obtain ⟨N,hN⟩:=exists_nat_gt ((2*((3*d:ℕ):ℝ))/(ζ/2))
  obtain ⟨ms,hms,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ N
  refine ⟨max mm ms,by omega,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q i hi pR pH θ εR εH βe βh
    hpRlo hpR1 hpHlo hθ hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh I J c L
  have hI0:(0:ℝ)≤I.card:=by positivity
  have hJ0:(0:ℝ)≤J.card:=by positivity
  have hc0:0≤c:=by dsimp [c];exact mul_nonneg hδ.le (le_min hI0 hJ0)
  have hcI:c≤δ*I.card:=by dsimp [c];exact mul_le_mul_of_nonneg_left (min_le_left _ _) hδ.le
  have hcJ:c≤δ*J.card:=by dsimp [c];exact mul_le_mul_of_nonneg_left (min_le_right _ _) hδ.le
  have hs:=hsize V U P D m hreg hn hD hρlo hρhi (by omega) Q i hi
  have hNI:(N:ℝ)≤I.card:=by
    have he:0≤ε*(I.card:ℝ):=mul_nonneg hε.le hI0
    have hh:=hs.2.1
    change (N:ℝ)≤(1-ε)*I.card at hh
    nlinarith only [he,hh]
  have hconst:2*((3*d:ℕ):ℝ)≤(ζ/2)*I.card:=by
    have hN':2*((3*d:ℕ):ℝ)<(ζ/2)*(N:ℝ):=by
      have hh:2*((3*d:ℕ):ℝ)<(N:ℝ)*(ζ/2):=
        (div_lt_iff₀ (show 0<ζ/2 by positivity)).mp hN
      nlinarith only [hh]
    have hm:=mul_le_mul_of_nonneg_left hNI (show 0≤ζ/2 by positivity)
    linarith
  have hL0:0≤L:=by dsimp [L];positivity
  have hL:L≤ζ*I.card:=by
    have hh:=mul_le_mul_of_nonneg_right hδζ hI0
    dsimp [L]
    nlinarith only [hconst,hcI,hh]
  have hcostI:c≤δm*I.card:=hcI.trans (mul_le_mul_of_nonneg_right hδm' hI0)
  have hcostJ:c≤δm*J.card:=hcJ.trans (mul_le_mul_of_nonneg_right hδm' hJ0)
  have hn:=hmain V U P D m hreg hn hD hρlo hρhi (by omega) Q i hi pR pH θ εR εH βe βh c
    hpRlo hpR1 hpHlo hθ hεR0 (hεR.trans hδm') hεH0 (hεH.trans hδm')
    hβe0 (hβe.trans hδm') hβh0 (hβh.trans hδm') hc0 hcostI hcostJ
  exact ⟨hc0,hcI,hcJ,hL0,hL,hn.1,hn.2.1,hn.2.2⟩
end Oberwolfach
