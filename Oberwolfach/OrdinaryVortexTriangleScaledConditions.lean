module

public import Oberwolfach.OrdinaryTriangleScaledConditionsFromInnerCleanup
public import Oberwolfach.OrdinaryVortexTriangleInnerSizeAndIndices

@[expose] public section
/-! At an actual fixed-vortex level, the inner-factor margin gives the
scaled numerical conditions for the sampled triangle cover-down. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D mv:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U P D β ε mv)

theorem ordinary_vortex_triangle_scaled_conditions
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv) (i:ℕ) (hi:i<Q.length)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (pmin pR pH density tR tH L Ledit βe βh δ εcount:ℝ)
    (p εsup τ ν η ell ζ:ℝ) (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hζ:0<ζ)
    (s:markedVortexHubType Q i→Color→ℝ)
    (raw:RawWheelOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color)
    (R F:SimpleGraph (markedVortexVertexType Q i)) (H:markedVortexVertexType Q i→markedVortexHubType Q i→Prop):
    let f:=markedVortexVertexEmbedding Q i;let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let ρi:=markedVortexPermutation Q π hπ i;let Ploc:=P.comap f;
    let γ:=min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4);
    let θ:=ζ*(γ/4)*ε;
    OrdinaryCleanupParentProfiles Ploc R F H ρi d I B pR pH density tR tH Ledit βe βh s j raw→
    RawOrdinaryRows Ploc ρi d 3 I pR s j tR raw→
    EndpointPhysicalEditedConditions Ploc R F H I B Iᶜ ρi d j (ρ₀/8) pmin pR pH L Ledit δ raw→
    pmin≤1→(3/4:ℝ)≤density→tR+4*Ledit≤εcount*I.card→tH+3*Ledit≤εcount*B.card→
    L≤(I.card:ℝ)/24→εcount≤min (pmin^4/16) (pmin^3/2)→(∀v,(F.degree v:ℝ)≤L)→
    (∀x∉I,∀v∈insert x I,(3/4:ℝ)*I.card≤((I∩Ploc.neighborFinset v).card:ℝ))→
    εsup≤p^2/4→τ+ν≤p^2/4→τ+ν+ell≤θ*p/4→ν+η≤θ*p/4→p≤4*θ→
    20*Real.sqrt (2*p)≤θ/2→2≤θ*p*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)/4→
    OrdinaryTriangleRootFirstScaledConditions R H I B p εsup τ ν η ell ((γ/4)*ε) ζ:=by
  intro f I B ρi Ploc γ θ profile deep geom hpmin1 hdensity hrow hindex hLA hεcount hF hdeg
    hεsup hsupport hclass hblock hpκ hsqrt horder
  have hsize:((ε/4)*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):ℝ)≤I.card:=
    (ordinary_vortex_triangle_inner_size_and_indices Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi).1
  exact ordinary_triangle_scaled_conditions_from_inner_cleanup Ploc R F H I B ρi d j s (ρ₀/8) pmin pR pH density
    tR tH L Ledit βe βh δ εcount raw profile deep geom hpmin1 hdensity hrow hindex hLA hεcount hF hdeg
    ε p εsup τ ν η ell ζ hε hp hp1 hτ hζ hsize hεsup hsupport hclass hblock hpκ hsqrt horder
end Oberwolfach
