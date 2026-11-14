module

public import Oberwolfach.OrdinaryInnerHubWeightsAmbientTransfer
public import Oberwolfach.OrdinaryInitialCorrectedSampleEditBothBalanceScaledProfile
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

theorem ordinary_initial_edit_both_balance_scaled_profile_inner_weights
    (mWheel d:ℕ) (ρ₀ α pmin:ℝ) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin):
    ∃cProfile:ℝ,0<cProfile ∧
    ∀ε:ℝ,0<ε→ε<1/4→∀η:ℝ,0<η→∃δ:ℝ,0<δ ∧ δ≤α ∧
    ∀(ζ δcap:ℝ),0<ζ→0≤δcap→δcap≤ζ/2→ζ≤δ→ζ≤δ*(ρ₀/8)→0<δcap→
    ∀ξlimit:ℝ,0<ξlimit→∃ξ:ℝ,0<ξ ∧ ξ≤ξlimit ∧
    ∀m t aK bK:ℕ,∀β:ℝ,0≤β→β≤1/4→β≤δ→∃v₀ N:ℕ,1≤v₀ ∧ 1≤N ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→N≤Fintype.card V→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (j:Color) (σ:RawWheelOutcome V U Γ Color) (s:U→Color→ℝ)
      (pR pH θ εR εH βe βh b Bweight Binner ηHub Kdom:ℝ),
      pmin≤pR→pR≤1→pmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cProfile*ε→0≤βh→βh≤cProfile*ε→
    ∀(A Z Wterm:Finset V) (Bterm Bprotect:Finset U),
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let raw:=ordinaryRawRestrictPair f g σ;let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    0<I.card→0≤b→0≤Binner→0≤Kdom→
    (Fintype.card (markedVortexVertexType Q 0):ℝ)≤Kdom*I.card→Binner*Kdom^mWheel≤Bweight→
    OrdinaryCorrectedProtectedReservoir (mWheel+1) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D vsize β ε Q π hπ pR pH s j σ→
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent mWheel (P.comap f) (F.comap f) I B ρi d pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh b Binner ηHub (fun u=>s (g u)) j raw→
    ∃(K:Finset (Sym2 V⊕(V×U))) (JQ:SimpleGraph V) (JH:V→U→Prop),
    OrdinaryCorrectedProtectedReservoirWitness (mWheel+1) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect K JQ JH ∧
    let Qcorr:=(R\F)\JQ;let Hcorr:=fun v u=>J v u∧¬JH v u;
    let G:=Qcorr\ordinaryResourceRim Qcorr K;let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    G≤P ∧ Disjoint G F ∧
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) ∧
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card) ∧
    0≤L ∧ L≤ζ*I.card ∧
    (∀w:markedVortexVertexType Q 0⊕markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρi d raw j)).neighborFinset w)
        ((ordinaryPhysicalGraph (G.comap f) (fun v u=>Hs (f v) (g u))).neighborFinset w)).card:ℝ)≤L) ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u)) ρi d I B
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card) L βe βh (fun u=>s (g u)) j raw ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η*I.card) ∧
    (∀v∉I,|(((G.comap f).neighborFinset v∩I).card:ℝ)-2*(B.filter (fun u=>Hs (f v) (g u))).card|≤η*I.card) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel b Binner ηHub (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I B) :=by
  obtain ⟨cProfile,hProfile,hmain⟩:=ordinary_initial_corrected_sample_edit_both_balance_scaled_profile mWheel d ρ₀ α pmin hρ₀ hα hpmin
  refine ⟨cProfile,hProfile,?_⟩
  intro ε hε hε1 η hη
  obtain ⟨δ,hδ,hδα,hmain⟩:=hmain ε hε hε1 η hη
  refine ⟨δ,hδ,hδα,?_⟩
  intro ζ δcap hζ hδcap0 hδcapζ hζδ hζB hδcap ξlimit hξlimit
  obtain ⟨ξ,hξ,hξlimit,hmain⟩:=hmain ζ δcap hζ hδcap0 hδcapζ hζδ hζB hδcap ξlimit hξlimit
  refine ⟨ξ,hξ,hξlimit,?_⟩
  intro m t aK bK β hβ hβ1 hβδ
  obtain ⟨v₀,N,hv₀,hN,hmain⟩:=hmain (2^(t*t)*aK) (2^(t*t)*bK) β hβ hβ1 hβδ
  refine ⟨v₀,N,hv₀,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv hnN Q π hπ j σ s
    pR pH θ εR εH βe βh b Bweight Binner ηHub Kdom hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect F R J f g ρi I B raw L hIpos hb hBinner hKdom hsize hBweight hRes hgood hevent
  obtain ⟨K,JQ,JH,hw⟩:=ordinary_corrected_reservoir_has_witness (mWheel+1) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect hRes
  have hw':=hw
  rcases hw' with ⟨hK,havoid,hrows,hhubs,hrowsloc,hdec,habs,hJQ,hJQavoid,hJH,hprotect,hbal,hdiv,hrow,hcol⟩
  have hAmbient:=ordinary_inner_hub_weight_event_ambient_transfer mWheel (P.comap f) (F.comap f) I B ρi d
    pR pH (θ+α-β/2) (εR*I.card) (εH*B.card) L βe βh b Binner Bweight ηHub Kdom (fun u=>s (g u)) j raw
    hIpos hb hBinner hKdom hsize hBweight hevent
  have hout:=hmain V U Γ Color P D vsize hreg hn hD hρlo hρhi hv hnN Q π hπ j σ s
    pR pH θ εR εH βe βh b Bweight ηHub hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
    JQ JH K hrow hcol hrows hhubs hprotect hdec
    (by intro v;convert hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hdiv u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hgood hAmbient
  let Qcorr:=(R\F)\JQ
  let Hcorr:=fun v u=>J v u∧¬JH v u
  let G:=Qcorr\ordinaryResourceRim Qcorr K
  let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K)
  rcases hout with ⟨hGP,hdis,hbal',hdiv',hL0,hLζ,hphysical,hlocal,hnear,hcross,_⟩
  have hGP':G.comap f≤P.comap f:=by intro x y hxy;exact hGP hxy
  letI : DecidableEq (markedVortexVertexType Q 0):=Classical.decEq _
  have hlocal':OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρi d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh (fun u=>s (g u)) j raw:=by
    convert hlocal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hweights:=hevent (G.comap f) (fun v u=>Hs (f v) (g u)) hlocal' hGP'
  refine ⟨K,JQ,JH,hw,?_⟩
  refine ⟨hGP,hdis,hbal',hdiv',hL0,hLζ,hphysical,hlocal,hnear,hcross,?_⟩
  convert hweights using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
