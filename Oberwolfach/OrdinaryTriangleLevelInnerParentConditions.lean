module

public import Oberwolfach.OrdinaryFixedVortexTriangleInnerParent
public import Oberwolfach.OrdinaryVortexTriangleScaledConditions
public import Oberwolfach.OrdinaryFixedVortexRowIndexEvent

@[expose] public section
/-! Every level uses the same inner-domain parent and scaled cover conditions;
its row tests are taken from the same raw outcome and its actual local host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_level_inner_parent_conditions
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D mv:ℕ) (β ε ρ₀:ℝ)
    (Q:Vortex U P D β ε mv) (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D)
    (hρhi:initialIndexDensity U D≤1) (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv) (i:ℕ) (hi:i<Q.length)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (α pmin εfactor ηend εrows δ εcount t lam:ℝ)
    (hα:0<α) (hβα:β≤α/8) (hpmin:0<pmin)
    (num:OrdinaryTriangleInnerNumericParameters pmin (ρ₀/8) εfactor ηend εrows δ εcount t lam)
    (hβbalance:β≤2*δ*(ρ₀/8)*pmin)
    (M:ℕ) (hM:32≤M) (hMε:4/ε≤(M:ℝ))
    (hMb:((2*(3*d):ℕ):ℝ)≤lam*M) (hterminal:(M:ℝ)≤ε*mv/2)
    (θhost pR pH εR εH Ledit tP rateParent βe βh:ℝ)
    (hθ:cycleThreshold 3≤θhost) (hdegree:(θhost+α)*Fintype.card V≤D)
    (hpR:pmin≤pR) (hpR1:pR≤1) (hpH:pmin≤pH) (hpH1:pH≤1)
    (hpEq:pR=initialIndexDensity U D*pH) (hεR:2*εR≤εcount) (hεH:2*εH≤εcount)
    (hE:0≤Ledit) (hrate:rateParent≤lam*ε/4) (htP:tP≤t)
    (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D mv β ε Q π hπ pR pH s j σ)
    (R:SimpleGraph (markedVortexVertexType Q i)) (H:markedVortexVertexType Q i→markedVortexHubType Q i→Prop)
    (p εsup τ ν η ell ζfresh:ℝ) (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hζfresh:0<ζfresh):
    let F:=permutationConflictGraph π (3*d);let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let ρi:=markedVortexPermutation Q π hπ i;let Ploc:=P.comap f;let Floc:=F.comap f;
    let raw:=ordinaryRawRestrictPair f g σ;let density:=θhost+α-β/2;let L:ℝ:=2*((3*d:ℕ):ℝ);
    let γ:=min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4);let θmatch:=ζfresh*(γ/4)*ε;
    OrdinaryCleanupParentProfiles Ploc R Floc H ρi d I B pR pH density
      (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j raw→
    R≤Ploc\Floc→
    Ledit≤rateParent*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)→
    εsup≤p^2/4→τ+ν≤p^2/4→τ+ν+ell≤θmatch*p/4→ν+η≤θmatch*p/4→p≤4*θmatch→
    20*Real.sqrt (2*p)≤θmatch/2→
    2≤θmatch*p*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)/4→
    EndpointPhysicalEditedConditions Ploc R Floc H I B Iᶜ ρi d j (ρ₀/8) pmin pR pH L Ledit δ raw ∧
    OrdinaryTriangleRootFirstScaledConditions R H I B p εsup τ ν η ell ((γ/4)*ε) ζfresh ∧
    I.Nonempty ∧ M≤I.card ∧
    Fintype.card {v:markedVortexVertexType Q i // v∉I}≤I.card^2 ∧
    Fintype.card {u:markedVortexHubType Q i // u∉B}≤I.card^2 ∧
    (∀v,Floc.degree v≤2*(3*d)) ∧ (∀v,(Floc.degree v:ℝ)≤L) ∧
    (εR*I.card)+4*Ledit≤εrows*I.card ∧ (εH*B.card)+3*Ledit≤εrows*B.card ∧
    L≤(I.card:ℝ)/24 ∧ L≤εfactor*I.card ∧
    δ+(2*40+(1+2*40)/(2*(ρ₀/8)*pmin))*L/I.card+
      (tP+10*(40/((ρ₀/8)*pmin^5))*Ledit/I.card)≤ηend ∧
    (3/4:ℝ)≤density ∧
    (∀x∉I,∀v∈insert x I,(3/4:ℝ)*I.card≤((I∩Ploc.neighborFinset v).card:ℝ)):=by
  intro F f g I B ρi Ploc Floc raw density L γ θmatch profile hQ hEdit hεsup hsupport hclass hblock hpκ hsqrt horder
  have hparent:=ordinary_fixed_vortex_triangle_inner_parent Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
    π hπ d α pmin εfactor ηend εrows δ εcount t lam hα hβα hpmin num hβbalance M hM hMε hMb hterminal
    θhost pR pH εR εH Ledit tP rateParent βe βh hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hεH hE hrate hEdit
    htP j (fun u=>s (g u)) raw R H profile hQ
  obtain ⟨geom,hI,hIs,hIv,hBu,hFnat,hF,hrowCount,hindexCount,hrow,hindex,hLA,hLfactor,herr,hdensity,hdeg⟩:=hparent
  have hrows:RawOrdinaryRows Ploc ρi d 3 I pR (fun u=>s (g u)) j (εR*I.card) raw:=(hgood i hi).1
  have hnum:=ordinary_vortex_triangle_scaled_conditions Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
    π hπ d j pmin pR pH density (εR*I.card) (εH*B.card) L Ledit βe βh δ εcount
    p εsup τ ν η ell ζfresh hp hp1 hτ hζfresh (fun u=>s (g u)) raw R Floc H
    profile hrows geom (hpR.trans hpR1) hdensity hrowCount hindexCount hLA num.count_geometry hF hdeg
    hεsup hsupport hclass hblock hpκ hsqrt horder
  exact ⟨geom,hnum,hI,hIs,hIv,hBu,hFnat,hF,hrow,hindex,hLA,hLfactor,herr,hdensity,hdeg⟩
end Oberwolfach
