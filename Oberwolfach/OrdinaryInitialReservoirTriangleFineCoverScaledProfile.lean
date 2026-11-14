module

public import Oberwolfach.OrdinaryInitialEditBothBalanceScaledProfileInnerWeights
public import Oberwolfach.MarkedFixedVortexEventInputs
public import Oberwolfach.OrdinaryVortexPairingParentFromProfileAt
public import Oberwolfach.OrdinaryInitialProfileWithCorrectedReservoir
public import Oberwolfach.OrdinaryVortexInitialBufferedTriangleSeparateLoadFineCover
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

theorem ordinary_initial_reservoir_buffered_triangle_fine_cover_scaled_profile
    (buffer d:ℕ) (ρ₀ α pmin δcut:ℝ)
    (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (hδcut:0<δcut) (hδsmall:δcut<1/4):
    ∃cProfile:ℝ,0<cProfile ∧
    ∀ε:ℝ,0<ε→ε<1/4→∀(ξroot:ℝ),0<ξroot→ξroot≤ε/100→∀(ηlimit:ℝ),0<ηlimit→
    ∃η₀:ℝ,0<η₀ ∧ η₀≤ηlimit ∧ ∃n₀:ℕ,∃δ:ℝ,0<δ ∧ δ≤α ∧
    ∀(Kdom ηf b Binner βe βh:ℝ),0<ηf→0≤b→0≤Binner→
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→
    ∀(ζ δcap:ℝ),0<ζ→0≤δcap→δcap≤ζ/2→ζ≤δ→ζ≤δ*(ρ₀/8)→0<δcap→
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
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cProfile*ε→0≤βh→βh≤cProfile*ε→
    ∀(A Z Wterm:Finset V) (Bterm Bprotect:Finset U)
      (coins:Sym2 V→Bool) (κ aLoad ζlimit ζcut εcut href αcut pstar:ℝ),
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let raw:=ordinaryRawRestrictPair f g σ;let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    OrdinaryNonrootNumericInputs (F.comap f) I (ordinaryVortexBufferedVertices Q 0 buffer) B (ordinaryVortexBufferedHubs Q 0 buffer)
      n₀ d (ρ₀/8) κ κ κ aLoad ζlimit ε δcut ζcut εcut pH εR εH L href→
    OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κ aLoad P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices 1) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    0<aLoad→aLoad≤1→80*ξroot≤aLoad^2→
    OrdinaryCorrectedProtectedReservoir (2+1) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D vsize β ε Q π hπ pR pH s j σ→
    OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P F D vsize β ε Q π hπ pR pH s j σ→
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent 2 (P.comap f) (F.comap f) I B ρi d pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh b Binner ηf (fun u=>s (g u)) j raw→
    ∃(K:Finset (Sym2 V⊕(V×U))) (JQ:SimpleGraph V) (JH:V→U→Prop),
    OrdinaryCorrectedProtectedReservoirWitness (2+1) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect K JQ JH ∧
    let Qcorr:=(R\F)\JQ;let Hcorr:=fun v u=>J v u∧¬JH v u;
    let G:=Qcorr\ordinaryResourceRim Qcorr K;let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    (G≤P ∧ Disjoint G F ∧
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) ∧
    (∀u,(2+1)∣(Finset.univ.filter (fun v=>Hs v u)).card) ∧
    0≤L ∧ L≤ζ*I.card ∧
    (∀w:markedVortexVertexType Q 0⊕markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρi d raw j)).neighborFinset w)
        ((ordinaryPhysicalGraph (G.comap f) (fun v u=>Hs (f v) (g u))).neighborFinset w)).card:ℝ)≤L) ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u)) ρi d I B
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card) L βe βh (fun u=>s (g u)) j raw ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η₀*I.card) ∧
    (∀v∉I,|(((G.comap f).neighborFinset v∩I).card:ℝ)-2*(B.filter (fun u=>Hs (f v) (g u))).card|≤η₀*I.card) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale 2 b Binner ηf (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I B)) ∧
    OrdinaryFineWheelCoverResult 2 0 ξroot aLoad (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I (ordinaryVortexBufferedVertices Q 0 buffer) B (ordinaryVortexBufferedHubs Q 0 buffer) ∧
    (∀v,|(((G.comap f).neighborFinset v∩ordinaryVortexBufferedVertices Q 0 2).card:ℝ)-
      2*((ordinaryVortexBufferedHubs Q 0 2).filter (fun u=>Hs (f v) (g u))).card|≤
      (initialIndexDensity U D*pH)*β*(ordinaryVortexBufferedVertices Q 0 2).card+
      εR*(ordinaryVortexBufferedVertices Q 0 2).card+2*(εH*(ordinaryVortexBufferedHubs Q 0 2).card)+3*L) :=by
  obtain ⟨cProfile,hProfile,hmain⟩:=ordinary_initial_edit_both_balance_scaled_profile_inner_weights 2 d ρ₀ α pmin hρ₀ hα hpmin
  refine ⟨cProfile,hProfile,?_⟩
  intro ε hε hε1 ξroot hξroot hξε ηlimit hηlimit
  obtain ⟨ηCover,hηCoverEq,hηCover,n₀,hcover⟩:=ordinary_vortex_initial_buffered_triangle_separate_load_fine_cover buffer ρ₀ ε δcut ξroot
    hρ₀ hε hδcut hδsmall hξroot hξε
  let η₀:=min ηCover ηlimit
  have hη₀:0<η₀:=lt_min hηCover hηlimit
  have hηcover:η₀≤ηCover:=min_le_left _ _
  have hηlimit':η₀≤ηlimit:=min_le_right _ _
  obtain ⟨δ,hδ,hδα,hmain⟩:=hmain ε hε hε1 η₀ hη₀
  refine ⟨η₀,hη₀,hηlimit',n₀,δ,hδ,hδα,?_⟩
  intro Kdom ηf b Binner βe βh hηf hb hBinner hKdom
  intro ζ δcap hζ hδcap0 hδcapζ hζδ hζB hδcap ξlimit hξlimit
  obtain ⟨ξ,hξ,hξlimit,hmain⟩:=hmain ζ δcap hζ hδcap0 hδcapζ hζδ hζB hδcap ξlimit hξlimit
  refine ⟨ξ,hξ,hξlimit,?_⟩
  intro m t aK bK β hβ hβ1 hβδ
  obtain ⟨v₀,N,hv₀,hN,hmain⟩:=hmain m t aK bK β hβ hβ1 hβδ
  obtain ⟨vSize,hvSize,hSize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ 1
  refine ⟨max v₀ vSize,N,by omega,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv hnN Q π hπ j σ s
    pR pH θ εR εH hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect coins κ aLoad ζlimit ζcut εcut href αcut pstar F R J f g ρi I B raw L
    hnums hDeep hRim hpH1 hεcut hζcut hζlimit hδlim hhref haLoad haLoad1 hξsmall hRes hgood hgood2 hevent
  have hsize:=hSize V U P D vsize hreg hn hD hρlo hρhi (by omega) Q 0 Q.length_pos
  have hIpos:0<I.card:=by
    have hh:=hsize.2.1
    by_contra h
    have hzero:I.card=0:=Nat.eq_zero_of_not_pos h
    have hzero':(markedVortexInnerVertices Q 0).card=0:=by
      convert hzero using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    simp [hzero'] at hh
    norm_num at hh
  have hK0:0≤Kdom:=by
    have hh:=hsize.1
    linarith
  have hratio:(Fintype.card (markedVortexVertexType Q 0):ℝ)≤Kdom*I.card:=by
    have hh:=mul_le_mul_of_nonneg_right hKdom (show (0:ℝ)≤I.card by positivity)
    exact hsize.2.2.2.1.trans hh
  obtain ⟨K,JQ,JH,hw,hprofile⟩:=hmain V U Γ Color P D vsize hreg hn hD hρlo hρhi (by omega) hnN Q π hπ j σ s
    pR pH θ εR εH βe βh b (Binner*Kdom^2) Binner ηf Kdom hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect hIpos hb hBinner hK0 hratio le_rfl hRes hgood hevent
  let Qcorr:=(R\F)\JQ
  let Hcorr:=fun v u=>J v u∧¬JH v u
  let G:=Qcorr\ordinaryResourceRim Qcorr K
  let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K)
  have hprofile':=hprofile
  rcases hprofile' with ⟨hGP,hdis,hbal,hdiv,hL0,hLζ,hphysical,hlocal,hnear,hcross,hHub⟩
  have hvsize:0<vsize:=by omega
  have hc:=hcover η₀ hη₀.le hηcover V U Γ Color P G Hs D vsize β hreg hn hD hρlo hρhi hβ hβ1 hvsize
    Q π hπ σ coins d j s κ aLoad ζlimit pR pH (θ+α-β/2) εR εH L βe βh ζcut εcut href αcut pstar
    hnums hlocal (by intro v;convert hnear v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hGP
    (by intro v;convert hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hdiv u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hDeep hRim (hpmin.trans_le hpH) hpH1 hεcut hζcut hζlimit hL0 hδlim hhref haLoad haLoad1 hξsmall
  have hρpos:0< initialIndexDensity U D:=lt_of_lt_of_le hρ₀ hρlo
  have hdeepBal:=ordinary_vortex_initial_zero_two_step_deep_balance P F D vsize β ε pR pH εR εH L Q π hπ d s j σ
    hn hreg hρpos hβ (hpmin.trans_le hpH).le hεR0 hεH0 hL0 hpEq hgood2
    (G.comap f) (fun v u=>Hs (f v) (g u))
    (by intro w;convert hphysical w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  refine ⟨K,JQ,JH,hw,?_,?_,?_⟩
  · convert hprofile using 1 <;> congr! 40
  · convert hc using 1 <;> congr! 40
  · intro v;convert hdeepBal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
