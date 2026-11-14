module

public import Oberwolfach.OrdinaryInitialEditBothBalanceProfileWithReservoir
public import Oberwolfach.OrdinaryVortexPairingParentFromProfileAt
public import Oberwolfach.OrdinaryInitialProfileWithCorrectedReservoir
public import Oberwolfach.OrdinaryVortexInitialBufferedFineCover
public import Oberwolfach.OrdinaryVortexInitialZeroTwoStepDeepBalance
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

theorem ordinary_initial_reservoir_buffered_fine_cover_all_balances_and_parent
    (mWheel Kdeep buffer d:ℕ) (hm:3≤mWheel) (ε ρ₀ α pmin δcut ξroot:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin)
    (hδcut:0<δcut) (hδsmall:δcut<1/4) (hξroot:0<ξroot) (hξε:ξroot≤ε/100)
    (ηlimit:ℝ) (hηlimit:0<ηlimit):
    ∃η₀:ℝ,0<η₀ ∧ η₀≤ηlimit ∧ ∃n₀:ℕ,∃δ:ℝ,0<δ ∧ δ≤α ∧
    ∀(Kdom ηf εf γ κ aPair lam b Bweight βe βh:ℝ),
      0<ηf→0<εf→0≤γ→0≤κ→0<aPair→0<lam→
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→
      aPair*(2*Kdom)+2*lam≤pmin/2→aPair*(2*Kdom)+2*lam≤pmin*(ρ₀/8)→
      6*lam≤ηf*aPair→γ≤βe→κ≤βe→
    ∀(ζ δcap:ℝ),0<ζ→0≤δcap→δcap≤ζ/2→ζ≤δ→ζ≤δ*(ρ₀/8)→ζ≤lam→0<δcap→
    ∀ξlimit:ℝ,0<ξlimit→∃ξ:ℝ,0<ξ ∧ ξ≤ξlimit ∧
    ∀m t aK bK:ℕ,∀β:ℝ,0≤β→β≤1/4→β≤δ→∃v₀ N:ℕ,1≤v₀ ∧ 1≤N ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→N≤Fintype.card V→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (j:Color) (σ:RawWheelOutcome V U Γ Color) (s:U→Color→ℝ)
      (pR pH θ εR εH:ℝ),
      pmin≤pR→pR≤1→pmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→εR≤lam→0≤εH→εH≤δ→εH≤lam→0≤βe→βe≤δ→0≤βh→βh≤δ→
    ∀(A Z Wterm:Finset V) (Bterm Bprotect:Finset U)
      (coins:Sym2 V→Bool) (a aLoad ρ θdeep ζlimit ζcut εcut href αcut pstar:ℝ),
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let raw:=ordinaryRawRestrictPair f g σ;let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    OrdinaryNonrootNumericInputs (F.comap f) I (ordinaryVortexBufferedVertices Q 0 buffer) B (ordinaryVortexBufferedHubs Q 0 buffer)
      n₀ d (ρ₀/8) a ρ θdeep aLoad ζlimit ε δcut ζcut εcut pH εR εH L href→
    OrdinaryFixedVortexDeepCoverEvent mWheel Kdeep d a aLoad ρ θdeep P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices 1) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    0<aLoad→aLoad≤1→80*ξroot≤aLoad^2→
    OrdinaryCorrectedProtectedReservoir (mWheel+1) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D vsize β ε Q π hπ pR pH s j σ→
    OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P F D vsize β ε Q π hπ pR pH s j σ→
    OrdinaryAdaptiveHubWeightsLevelEvent mWheel (P.comap f) (F.comap f) I B ρi d pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh b Bweight ηf (fun u=>s (g u)) j raw→
    ∃(K:Finset (Sym2 V⊕(V×U))) (JQ:SimpleGraph V) (JH:V→U→Prop),
    OrdinaryCorrectedProtectedReservoirWitness (mWheel+1) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect K JQ JH ∧
    let Qcorr:=(R\F)\JQ;let Hcorr:=fun v u=>J v u∧¬JH v u;
    let G:=Qcorr\ordinaryResourceRim Qcorr K;let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    (G≤P ∧ Disjoint G F ∧
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) ∧
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card) ∧
    0≤L ∧ L≤ζ*I.card ∧
    (∀w:markedVortexVertexType Q 0⊕markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρi d raw j)).neighborFinset w)
        ((ordinaryPhysicalGraph (G.comap f) (fun v u=>Hs (f v) (g u))).neighborFinset w)).card:ℝ)≤L) ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u)) ρi d I B
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card) L βe βh (fun u=>s (g u)) j raw ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η₀*I.card) ∧
    (∀v∉I,|(((G.comap f).neighborFinset v∩I).card:ℝ)-2*(B.filter (fun u=>Hs (f v) (g u))).card|≤η₀*I.card) ∧
    Nonempty (OrdinaryMixedHubWeightsOfLength mWheel b Bweight ηf (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I B)) ∧
    OrdinaryFineWheelCoverResult mWheel Kdeep ξroot aLoad (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I (ordinaryVortexBufferedVertices Q 0 buffer) B (ordinaryVortexBufferedHubs Q 0 buffer) ∧
    Nonempty (MixedFreshPairingParentInsideRoots mWheel (2*(3*d)) γ κ b Bweight pmin aPair εf ηf
      (spanningRestriction (G.comap f) I) (F.comap f)
      (ordinaryPhysicalGraph (spanningRestriction (G.comap f) I) (fun v u=>Hs (f v) (g u)∧v∈I∧u∈B))
      (ordinaryPhysicalGraph (F.comap f) (fun _ _=>False)) (Function.Embedding.inl:markedVortexVertexType Q 0↪_)
      (ordinaryBoundaryHubSet (fun v u=>Hs (f v) (g u)) B I)
      (fun k=>(ordinaryBoundaryRimSet (G.comap f) I k).image Sum.inl)
      (fun k=>(ordinaryBoundaryRowSet (fun v u=>Hs (f v) (g u)) I B k).image Sum.inr) (fun _=>pH)) ∧
    (∀v,|(((G.comap f).neighborFinset v∩ordinaryVortexBufferedVertices Q 0 2).card:ℝ)-
      2*((ordinaryVortexBufferedHubs Q 0 2).filter (fun u=>Hs (f v) (g u))).card|≤
      (initialIndexDensity U D*pH)*β*(ordinaryVortexBufferedVertices Q 0 2).card+
      εR*(ordinaryVortexBufferedVertices Q 0 2).card+2*(εH*(ordinaryVortexBufferedHubs Q 0 2).card)+3*L) :=by
  obtain ⟨ηCover,hηCoverEq,hηCover,n₀,hcover⟩:=ordinary_vortex_initial_buffered_fine_cover mWheel Kdeep buffer hm ρ₀ ε δcut ξroot
    hρ₀ hε hδcut hδsmall hξroot hξε
  let η₀:=min ηCover ηlimit
  have hη₀:0<η₀:=lt_min hηCover hηlimit
  have hηcover:η₀≤ηCover:=min_le_left _ _
  have hηlimit':η₀≤ηlimit:=min_le_right _ _
  obtain ⟨δ,hδ,hδα,hmain⟩:=ordinary_initial_edit_both_balance_profile_with_corrected_reservoir mWheel d ε ρ₀ α pmin η₀ hε hε1 hρ₀ hα hpmin hη₀
  refine ⟨η₀,hη₀,hηlimit',n₀,δ,hδ,hδα,?_⟩
  intro Kdom ηf εf γ κ aPair lam b Bweight βe βh hηf hεf hγ hκ haPair hlam hKdom hRrate hHrate herr hγβ hκβ
  intro ζ δcap hζ hδcap0 hδcapζ hζδ hζB hζlam hδcap ξlimit hξlimit
  obtain ⟨ξ,hξ,hξlimit,hmain⟩:=hmain ζ δcap hζ hδcap0 hδcapζ hζδ hζB hδcap ξlimit hξlimit
  refine ⟨ξ,hξ,hξlimit,?_⟩
  intro m t aK bK β hβ hβ1 hβδ
  obtain ⟨v₀,N,hv₀,hN,hmain⟩:=hmain m t aK bK β hβ hβ1 hβδ
  obtain ⟨vPair,hvPair,hPair⟩:=ordinary_vortex_pairing_parent_from_profile_at ε ρ₀ pmin Kdom ηf εf γ κ aPair lam b Bweight βe βh d mWheel β
    hε hε1 hρ₀ hpmin hηf hεf hγ hκ haPair hlam hKdom hRrate hHrate herr hγβ hκβ hβ hβ1
  refine ⟨max v₀ vPair,N,by omega,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv hnN Q π hπ j σ s
    pR pH θ εR εH hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεRlam hεH0 hεH hεHlam hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect coins a aLoad ρ θdeep ζlimit ζcut εcut href αcut pstar F R J f g ρi I B raw L
    hnums hDeep hRim hpH1 hεcut hζcut hζlimit hδlim hhref haLoad haLoad1 hξsmall hRes hgood hgood2 hevent
  obtain ⟨K,JQ,JH,hw,hprofile⟩:=hmain V U Γ Color P D vsize hreg hn hD hρlo hρhi (by omega) hnN Q π hπ j σ s
    pR pH θ εR εH βe βh b Bweight ηf hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect hRes hgood hevent
  let Qcorr:=(R\F)\JQ
  let Hcorr:=fun v u=>J v u∧¬JH v u
  let G:=Qcorr\ordinaryResourceRim Qcorr K
  let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K)
  have hprofile':=hprofile
  rcases hprofile' with ⟨hGP,hdis,hbal,hdiv,hL0,hLζ,hphysical,hlocal,hnear,hcross,hHub⟩
  have hvsize:0<vsize:=by omega
  have hc:=hcover η₀ hη₀.le hηcover V U Γ Color P G Hs D vsize β hreg hn hD hρlo hρhi hβ hβ1 hvsize
    Q π hπ σ coins d j s a aLoad ρ θdeep ζlimit pR pH (θ+α-β/2) εR εH L βe βh ζcut εcut href αcut pstar
    hnums hlocal (by intro v;convert hnear v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hGP
    (by intro v;convert hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hdiv u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hDeep hRim (hpmin.trans_le hpH) hpH1 hεcut hζcut hζlimit hL0 hδlim hhref haLoad haLoad1 hξsmall
  have hLlam:L≤lam*I.card:=hLζ.trans (mul_le_mul_of_nonneg_right hζlam (by positivity))
  have hp:=hPair V U Γ Color P G Hs D vsize hreg hn hD hρlo hρhi (by omega) Q π hπ 0 Q.length_pos
    s j σ pR pH (θ+α-β/2) εR εH L hpR hpH hpH1 hεR0 hεRlam hεH0 hεHlam hL0 hGP hLlam
    (by convert hlocal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hevent using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hρpos:0< initialIndexDensity U D:=lt_of_lt_of_le hρ₀ hρlo
  have hdeepBal:=ordinary_vortex_initial_zero_two_step_deep_balance P F D vsize β ε pR pH εR εH L Q π hπ d s j σ
    hn hreg hρpos hβ (hpmin.trans_le hpH).le hεR0 hεH0 hL0 hpEq hgood2
    (G.comap f) (fun v u=>Hs (f v) (g u))
    (by intro w;convert hphysical w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  refine ⟨K,JQ,JH,hw,?_,?_,?_,?_⟩
  · convert hprofile using 1 <;> congr! 40
  · convert hc using 1 <;> congr! 40
  · convert hp using 1 <;> congr! 40
  · intro v;convert hdeepBal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
