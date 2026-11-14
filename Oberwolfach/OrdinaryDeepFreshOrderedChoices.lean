module

public import Oberwolfach.OrdinaryVortexTraceTriangleFreshBundleSized
public import Oberwolfach.OrdinaryDeepParentEarlyWeightsHierarchy

@[expose] public section
/-! Name the complete actual-trace fresh-bundle property so its choices can
    be ordered with the earlier deep-parent numeric hierarchy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryVortexTraceTriangleFreshProperty (γ κ b Bweight εf ηHub ζfresh:ℝ):Prop :=
    ∀(p:ℝ),0<p→p≤1→∀(εres εsup βe βh:ℝ),0<εres→0<εsup→0<βe→0<βh→∃Nfresh:ℕ,
    ∀    (ε ρ₀ α pmin η ζ δ δcap rate Kdom δparent εparent tpot lam:ℝ) (d:ℕ)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (hζlam:ζ≤lam) (hδcap0:0≤δcap)
    (hwitness:OrdinaryVortexTraceCapCostWitness ε ρ₀ α pmin pmin η ζ δ δcap rate d)
    (num:OrdinaryDeepNumericParameters pmin (ρ₀/8) (1/Kdom) ηHub εf (2*Kdom)
      γ κ δparent εparent tpot lam b Bweight),
∀β:ℝ,0≤β→β≤1/4→β≤δ→β≤α/8→β≤2*δparent*(ρ₀/8)*pmin→
    ∀C:ℝ,0≤C→∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (pR pH θ εR εH:ℝ),pmin≤pR→pR≤1→pmin≤pH→pH≤1→1/2≤θ→cycleThreshold 3≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→2*εR≤εparent→0≤εH→εH≤δ→2*εH≤εparent→0≤βe→βe≤δ→0≤βh→βh≤δ→
    ∀(K:Finset (Sym2 V⊕(V×U))),
      (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)→
      (∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))→
      Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
        D m β ε Q π hπ pR pH s j σ→
    ∀(cost deepCost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
    ∀(A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop),
    let F:=permutationConflictGraph π (3*d);
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    let I:=markedVortexInnerVertices Q (i+1);let B:=markedVortexInnerHubs Q (i+1);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A→
    ordinaryHostResources G Hs=A→
    ∀ν ηCover ρCover:ℝ,
    let parent:ℝ:=Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i);
    0≤ν→ν≤rate*parent→0≤ηCover→ηCover≤rate*parent→0≤ρCover→ρCover≤rate→
    cost i=ν+ηCover+(2*(ρCover*parent)+C)→
    OrdinaryAdaptiveHubWeightsLevelEvent 2 (P.comap f) (F.comap f) I B ρ d
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card)
      (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card) βe βh b Bweight ηHub (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ)→
    ∀(weight:markedVortexVertexType Q (i+1)→Sym2 (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))→ℝ),
    EndpointPhysicalParentWeights (P.comap f) I Iᶜ weight→
    EndpointPhysicalPotentialEvent (P.comap f) (F.comap f) I B Iᶜ ρ d j weight pR pH tpot
      (ordinaryRawRestrictPair f g σ)→
    (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card)≤ζ*I.card ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ) ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η*I.card) ∧
    Nonempty (OrdinaryMixedHubWeightsOfLength 2 b Bweight ηHub (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I B) ∧
    Nonempty (MixedFreshParentDataInsideRoots γ κ b Bweight εf ηHub
      (spanningRestriction (G.comap f) I) (F.comap f)
      (ordinaryPhysicalGraph (spanningRestriction (G.comap f) I)
        (fun v u=>Hs (f v) (g u)∧v∈I∧u∈B))
      (ordinaryPhysicalGraph (F.comap f) (fun _ _=>False)) (Function.Embedding.inl:markedVortexVertexType Q (i+1)↪_)
      (ordinaryBoundaryHubSet (fun v u=>Hs (f v) (g u)) B I)
      (fun k=>(ordinaryBoundaryRimSet (G.comap f) I k).image Sum.inl)
      (fun k=>(ordinaryBoundaryRowSet (fun v u=>Hs (f v) (g u)) I B k).image Sum.inr)) ∧
    ∃data:MixedFreshParentDataInsideRoots γ κ b Bweight εf ηHub
      (spanningRestriction (G.comap f) I) (F.comap f)
      (ordinaryPhysicalGraph (spanningRestriction (G.comap f) I)
        (fun v u=>Hs (f v) (g u)∧v∈I∧u∈B))
      (ordinaryPhysicalGraph (F.comap f) (fun _ _=>False)) (Function.Embedding.inl:markedVortexVertexType Q (i+1)↪_)
      (ordinaryBoundaryHubSet (fun v u=>Hs (f v) (g u)) B I)
      (fun k=>(ordinaryBoundaryRimSet (G.comap f) I k).image Sum.inl)
      (fun k=>(ordinaryBoundaryRowSet (fun v u=>Hs (f v) (g u)) I B k).image Sum.inr),
    ∃σfresh:Sym2 (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))→Bool,
      OrdinaryFreshTriangleBoundaryEventInside (G.comap f) (spanningRestriction (G.comap f) I) (F.comap f)
        (fun v u=>Hs (f v) (g u)) (fun v u=>Hs (f v) (g u)∧v∈I∧u∈B) I B
        γ κ b Bweight εf ηHub ζfresh p εres εsup βe βh data σfresh

theorem ordinary_vortex_trace_triangle_fresh_property
    (γ κ b Bweight:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hBweight:0≤Bweight):
    ∃εf ηHub ζfresh:ℝ,0<εf ∧ 0<ηHub ∧ 0<ζfresh ∧
      OrdinaryVortexTraceTriangleFreshProperty γ κ b Bweight εf ηHub ζfresh :=by
  exact ordinary_vortex_trace_triangle_fresh_bundle_from_common_sized γ κ b Bweight hγ hκ hb hBweight

theorem ordinary_deep_fresh_ordered_choices
    (pmin κe a K bcap Bmin:ℝ) (hp:0<pmin) (hκe:0<κe) (ha:0<a) (hK:0<K)
    (hbcap:0<bcap) (hBmin:0≤Bmin):
    ∃γ κ b B εf ηHub ζfresh δparent εparent tpot lam:ℝ,
      0<γ ∧ 0<κ ∧ 0<b ∧ b≤bcap ∧ 0<B ∧ Bmin≤B ∧
      0<εf ∧ 0<ηHub ∧ 0<ζfresh ∧
      OrdinaryDeepNumericParameters pmin κe a ηHub εf K γ κ δparent εparent tpot lam b B ∧
      OrdinaryVortexTraceTriangleFreshProperty γ κ b B εf ηHub ζfresh :=by
  obtain ⟨γ,κ,b,B,hγ,hκ,hb,hbcap,hB,hBmin,hNum⟩:=
    ordinary_deep_parent_early_weights_hierarchy pmin κe a K bcap Bmin hp hκe ha hK hbcap hBmin
  obtain ⟨εf,ηHub,ζfresh,hεf,hηHub,hζfresh,hFresh⟩:=
    ordinary_vortex_trace_triangle_fresh_property γ κ b B hγ hκ hb hB.le
  obtain ⟨δparent,εparent,tpot,lam,hNum⟩:=hNum ηHub εf hηHub hεf
  exact ⟨γ,κ,b,B,εf,ηHub,ζfresh,δparent,εparent,tpot,lam,hγ,hκ,hb,hbcap,hB,hBmin,hεf,hηHub,hζfresh,hNum,hFresh⟩
end Oberwolfach
