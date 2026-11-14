module

public import Oberwolfach.OrdinaryInitialTriangleCoverParentVortexMarginsEarlyVortex
public import Oberwolfach.OrdinaryFixedVortexNonrootNumericInputs

@[expose] public section
/-! Choose the nonroot numerical tolerances before the vortex, and derive
those hypotheses at the initial corrected triangle reservoir. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 90000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_triangle_cover_parent_numeric_hierarchy_early_vortex
    (d:ℕ) (ρ₀ α pmin κ:ℝ) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (hκ:0<κ) (hκ1:κ≤1):
    let αcut:=min (α/4) (1/4:ℝ)
    let href:=αcut*pmin/128
    let δlimit:=min (αcut/32) (pmin/512);
    ∃δcut ζcut εcut ζlimit εsample εvortex:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧
      0<ζlimit ∧ 0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧
    ∀(ε ξroot Kdom ηHub εf γparent κparent δparent εparent tpot lam b Bweight:ℝ),
    0<ε→ε≤εvortex→0<ξroot→ξroot≤ε/100→
    (1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom)→
    OrdinaryDeepNumericParameters pmin (ρ₀/8) (1/Kdom) ηHub εf (2*Kdom)
      γparent κparent δparent εparent tpot lam b Bweight→
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∃δ:ℝ,0<δ ∧ δ≤α ∧
    ∀(ζ δcap:ℝ),0<ζ→ζ≤ζlimit→0≤δcap→δcap≤ζ/2→ζ≤δ→ζ≤δ*(ρ₀/8)→ζ≤lam→0<δcap→
    ∀ξlimit:ℝ,0<ξlimit→∃ξ:ℝ,0<ξ ∧ ξ≤ξlimit ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→β≤α/8→β≤2*δparent*(ρ₀/8)*pmin→∃v₀:ℕ,1≤v₀ ∧ ∀m t aK bK:ℕ,∃N:ℕ,1≤N ∧
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
      0≤εR→εR≤δ→εR≤εsample→2*εR≤εparent→0≤εH→εH≤δ→εH≤εsample→2*εH≤εparent→0≤βe→βe≤δ→0≤βh→βh≤δ→
    ∀(A Z Wterm:Finset V) (Bterm Bprotect:Finset U)
      (coins:Sym2 V→Bool),
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let raw:=ordinaryRawRestrictPair f g σ;let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    ∀(weight:markedVortexVertexType Q 0→Sym2 (markedVortexVertexType Q 0⊕markedVortexHubType Q 0)→ℝ),
    EndpointPhysicalParentWeights (P.comap f) I Iᶜ weight→
    EndpointPhysicalPotentialEvent (P.comap f) (F.comap f) I B Iᶜ ρi d j weight pR pH tpot raw→
    OrdinaryFixedVortexTriangleNonrootCoverEvent d κ P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices 1) (sampledOrientation (rawWheelGraph P σ) coins) αcut pmin→
    pH≤1→80*ξroot≤κ^2→
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
      (fun i=>(ordinaryBoundaryRowSet (fun v u=>Hs (f v) (g u)) I B i).image Sum.inr)) := by
  intro αcut href δlimit
  have hαcut:0<min (α/4) (1/4:ℝ):=lt_min (by positivity) (by norm_num)
  have hhref:0<min (α/4) (1/4:ℝ)*pmin/128:=by positivity
  have hδlimit:0<min (min (α/4) (1/4:ℝ)/32) (pmin/512):=lt_min (by positivity) (by positivity)
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδlimitBound,hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hnum⟩:=
    ordinary_fixed_vortex_nonroot_numeric_inputs ρ₀ pmin
      (min (α/4) (1/4:ℝ)*pmin/128) (min (min (α/4) (1/4:ℝ)/32) (pmin/512))
      κ κ κ κ hρ₀ hpmin hhref hδlimit hκ hκ hκ hκ
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδlimitBound,hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,?_⟩
  intro ε ξroot Kdom ηHub εf γparent κparent δparent εparent tpot lam b Bweight hε hεv hξroot hξε hKdom num
  have hε1:ε<1/4:=lt_of_le_of_lt hεv hεvortex1
  obtain ⟨η₀,hη₀,n₀,δ,hδ0,hδα,hmain⟩:=ordinary_initial_triangle_cover_parent_from_vortex_margins_early_vortex
    d ε ρ₀ α pmin δcut ξroot Kdom ηHub εf γparent κparent δparent εparent tpot lam b Bweight
    hε hε1 hρ₀ hα hpmin hδ hδsmall hξroot hξε hKdom num
  refine ⟨η₀,hη₀,n₀,δ,hδ0,hδα,?_⟩
  intro ζ δcap hζ hζlim hδcap0 hδcapζ hζδ hζB hζlam hδcap ξlimit hξlimit
  obtain ⟨ξ,hξ,hξlimit,hmain⟩:=hmain ζ δcap hζ hδcap0 hδcapζ hζδ hζB hζlam hδcap ξlimit hξlimit
  refine ⟨ξ,hξ,hξlimit,?_⟩
  intro β hβ hβ1 hβδ hβα hβbal
  obtain ⟨v₀,hv₀,hmain⟩:=hmain β hβ hβ1 hβδ hβα hβbal
  obtain ⟨v₁,hv₁,hnumeric⟩:=hnum ε hε hεv β hβ hβ1 d n₀
  obtain ⟨v₂,hv₂,hcap⟩:=ordinary_vortex_canonical_edit_cap_small ε ρ₀ ζ δcap d hε hε1 hρ₀ hζ hδcap0 hδcapζ β hβ hβ1
  refine ⟨max (max v₀ v₁) v₂,by omega,?_⟩
  intro m t aK bK
  obtain ⟨N,hN,hmain⟩:=hmain m t aK bK
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv hnN Q π hπ j σ s
    pR pH θ εR εH βe βh hpR hpR1 hpH hθ hthreshold hdegree hpEq hs hεR0 hεR hεRs hεRp hεH0 hεH hεHs hεHp hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect coins F R J f g ρi I B raw L weight parent event hDeep hRim hpH1 hξsmall hRes hgood hevent
  have hcapLocal:=hcap V U P D vsize hreg hn hD hρlo hρhi (by omega) Q 0 Q.length_pos
  have hL:L≤ζlimit*I.card:=hcapLocal.2.trans (mul_le_mul_of_nonneg_right hζlim (by positivity))
  have hnumeric':=hnumeric V U P D vsize hreg hn hD hρlo hρhi (by omega) Q π hπ 0 Q.length_pos
    pH εR εH L hpH hεR0 hεRs hεH0 hεHs (by positivity) hL
  have hhrefle:min (α/4) (1/4:ℝ)*pmin/128≤min (α/4) (1/4:ℝ)*pmin/64:=by
    have hh:0≤min (α/4) (1/4:ℝ)*pmin:=mul_nonneg hαcut.le hpmin.le
    linarith
  exact hmain V U Γ Color P D vsize hreg hn hD hρlo hρhi (by omega) hnN Q π hπ j σ s
    pR pH θ εR εH βe βh hpR hpR1 hpH hθ hthreshold hdegree hpEq hs hεR0 hεR hεRp hεH0 hεH hεHp hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect coins κ ζlimit ζcut εcut (min (α/4) (1/4:ℝ)*pmin/128) (min (α/4) (1/4:ℝ)) pmin
    weight parent event hnumeric' hDeep hRim hpH1 hεcut.le hζcut.le hζlimit.le hδlimitBound hhrefle hκ hκ1 hξsmall hRes hgood hevent
end Oberwolfach
