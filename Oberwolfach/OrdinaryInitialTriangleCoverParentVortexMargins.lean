module

public import Oberwolfach.OrdinaryInitialReservoirTriangleCoverAndParent
public import Oberwolfach.OrdinaryFixedVortexDeepParentMargins
public import Oberwolfach.OrdinaryTriangleParentFromCommonLengthWeights
public import Oberwolfach.OrdinaryInitialReservoirTriangleNonrootCover
public import Oberwolfach.OrdinaryInitialProfileWithCorrectedReservoir
public import Oberwolfach.OrdinaryVortexInitialTriangleNonrootCover
public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness

@[expose] public section
/-! Retain the same selected absorber and correction when deriving the
initial local profile and adaptive hub weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_triangle_cover_parent_from_vortex_margins
    (d:ℕ) (ε ρ₀ α pmin δcut ξroot Kdom ηHub εf γparent κparent δparent εparent tpot lam b Bweight:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin)
    (hδcut:0<δcut) (hδsmall:δcut<1/4) (hξroot:0<ξroot) (hξε:ξroot≤ε/100)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom)
    (num:OrdinaryDeepNumericParameters pmin (ρ₀/8) (1/Kdom) ηHub εf (2*Kdom)
      γparent κparent δparent εparent tpot lam b Bweight):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∃δ:ℝ,0<δ ∧ δ≤α ∧
    ∀(ζ δcap:ℝ),0<ζ→0≤δcap→δcap≤ζ/2→ζ≤δ→ζ≤δ*(ρ₀/8)→ζ≤lam→0<δcap→
    ∀ξlimit:ℝ,0<ξlimit→∃ξ:ℝ,0<ξ ∧ ξ≤ξlimit ∧
    ∀m t aK bK:ℕ,∀β:ℝ,0≤β→β≤1/4→β≤δ→β≤α/8→β≤2*δparent*(ρ₀/8)*pmin→∃v₀ N:ℕ,1≤v₀ ∧ 1≤N ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→N≤Fintype.card V→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (j:Color) (σ:RawWheelOutcome V U Γ Color) (s:U→Color→ℝ)
      (pR pH θ εR εH βe βh:ℝ),
      pmin≤pR→pR≤1→pmin≤pH→1/2≤θ→cycleThreshold 3≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→2*εR≤εparent→0≤εH→εH≤δ→2*εH≤εparent→0≤βe→βe≤δ→0≤βh→βh≤δ→
    ∀(A Z Wterm:Finset V) (Bterm Bprotect:Finset U)
      (coins:Sym2 V→Bool) (κ ζlimit ζcut εcut href αcut pstar:ℝ),
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let raw:=ordinaryRawRestrictPair f g σ;let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    ∀(weight:markedVortexVertexType Q 0→Sym2 (markedVortexVertexType Q 0⊕markedVortexHubType Q 0)→ℝ),
    EndpointPhysicalParentWeights (P.comap f) I Iᶜ weight→
    EndpointPhysicalPotentialEvent (P.comap f) (F.comap f) I B Iᶜ ρi d j weight pR pH tpot raw→
    OrdinaryNonrootNumericInputs (F.comap f) I (markedVortexDeeperVertices Q 0) B (markedVortexDeeperHubs Q 0)
      n₀ d (ρ₀/8) κ κ κ κ ζlimit ε δcut ζcut εcut pH εR εH L href→
    OrdinaryFixedVortexTriangleNonrootCoverEvent d κ P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices 1) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    0<κ→κ≤1→80*ξroot≤κ^2→
    OrdinaryCorrectedProtectedReservoir (3) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D vsize β ε Q π hπ pR pH s j σ→
    OrdinaryAdaptiveHubWeightsLevelEvent 2 (P.comap f) (F.comap f) I B ρi d pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh b Bweight ηHub (fun u=>s (g u)) j raw→
    ∃(K:Finset (Sym2 V⊕(V×U))) (JQ:SimpleGraph V) (JH:V→U→Prop),
    OrdinaryCorrectedProtectedReservoirWitness (3) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect K JQ JH ∧
    let Qcorr:=(R\F)\JQ;let Hcorr:=fun v u=>J v u∧¬JH v u;
    let G:=Qcorr\ordinaryResourceRim Qcorr K;let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    (G≤P ∧ Disjoint G F ∧
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) ∧
    (∀u,(3)∣(Finset.univ.filter (fun v=>Hs v u)).card) ∧
    0≤L ∧ L≤ζ*I.card ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u)) ρi d I B
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card) L βe βh (fun u=>s (g u)) j raw ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η₀*I.card) ∧
    Nonempty (OrdinaryMixedHubWeightsOfLength 2 b Bweight ηHub (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I B)) ∧
    OrdinaryNonrootWheelCoverResult 2 0 ξroot κ (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I (markedVortexDeeperVertices Q 0) B (markedVortexDeeperHubs Q 0) ∧
    Nonempty (MixedFreshParentDataInsideRoots γparent κparent b Bweight εf ηHub
      (spanningRestriction (G.comap f) I) (F.comap f)
      (ordinaryPhysicalGraph (spanningRestriction (G.comap f) I)
        (fun v u=>Hs (f v) (g u)∧v∈I∧u∈B))
      (ordinaryPhysicalGraph (F.comap f) (fun _ _=>False)) (Function.Embedding.inl:markedVortexVertexType Q 0↪_)
      (ordinaryBoundaryHubSet (fun v u=>Hs (f v) (g u)) B I)
      (fun i=>(ordinaryBoundaryRimSet (G.comap f) I i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (fun v u=>Hs (f v) (g u)) I B i).image Sum.inr)) :=by
  obtain ⟨η₀,hη₀,n₀,δ,hδ,hδα,hmain⟩:=ordinary_initial_reservoir_triangle_cover_and_parent d ε ρ₀ α pmin δcut ξroot
    hε hε1 hρ₀ hα hpmin hδcut hδsmall hξroot hξε
  refine ⟨η₀,hη₀,n₀,δ,hδ,hδα,?_⟩
  intro ζ δcap hζ hδcap0 hδcapζ hζδ hζB hζlam hδcap ξlimit hξlimit
  obtain ⟨ξ,hξ,hξlimit,hmain⟩:=hmain ζ δcap hζ hδcap0 hδcapζ hζδ hζB hδcap ξlimit hξlimit
  refine ⟨ξ,hξ,hξlimit,?_⟩
  intro m t aK bK β hβ hβ1 hβδ hβα hβbalance
  obtain ⟨v₀,N,hv₀,hN,hmain⟩:=hmain m t aK bK β hβ hβ1 hβδ
  obtain ⟨v₁,hv₁,hmargin⟩:=ordinary_fixed_vortex_deep_parent_margins β ε ρ₀ α pmin Kdom ηHub εf
    γparent κparent δparent εparent tpot lam b Bweight hβ hβ1 hβα hε hε1 hρ₀ hα hpmin hKdom num hβbalance d
  obtain ⟨v₂,hv₂,hcap⟩:=ordinary_vortex_canonical_edit_cap_small ε ρ₀ ζ δcap d hε hε1 hρ₀ hζ hδcap0 hδcapζ β hβ hβ1
  refine ⟨max (max v₀ v₁) v₂,N,by omega,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv hnN Q π hπ j σ s
    pR pH θ εR εH βe βh hpR hpR1 hpH hθ hthreshold hdegree hpEq hs hεR0 hεR hεRsmall hεH0 hεH hεHsmall hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect coins κ ζlimit ζcut εcut href αcut pstar F R J f g ρi I B raw L
    weight parent event hnums hDeep hRim hpH1 hεcut hζcut hζlimit hδlim hhref hκ hκ1 hξsmall hRes hgood hevent
  have hcapLocal:=hcap V U P D vsize hreg hn hD hρlo hρhi (by omega) Q 0 Q.length_pos
  have hEdit:L≤lam*I.card:=hcapLocal.2.trans (mul_le_mul_of_nonneg_right hζlam (by positivity))
  have margins:=hmargin V U P D vsize hreg hn hD hρlo hρhi (by omega) Q π hπ θ pR pH εR εH L
    hthreshold hdegree hpR hpR1 hpH hpH1 hpEq hεR0 hεRsmall hεH0 hεHsmall (by positivity) 0 Q.length_pos hEdit
  have hout:=hmain V U Γ Color P D vsize hreg hn hD hρlo hρhi (by omega) hnN Q π hπ j σ s
    pR pH θ εR εH βe βh b Bweight ηHub hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect coins κ ζlimit ζcut εcut href αcut pstar weight γparent κparent εf (ρ₀/8) pmin
    (2*((3*d:ℕ):ℝ)) δparent εparent tpot (2*Kdom) (pR*β*I.card) margins parent event
    hnums hDeep hRim hpH1 hεcut hζcut hζlimit hδlim hhref hκ hκ1 hξsmall hRes hgood hevent
  convert hout using 1 <;> congr! 50
end Oberwolfach
