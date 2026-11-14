module

public import Oberwolfach.MarkedNeighbourhoodAdaptiveVortexEvent
public import Oberwolfach.VortexRemovedStarSizes

@[expose] public section

/-! One retained experiment supplies both neighbourhood families on every
fixed level and for every subsequent admissible physical deletion. The
quantifier over deletions follows the sampled outcome, and external roots
remain in the bounds into the specified row and index domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_neighbourhood_active_vortex_event
    (h d : ℕ) (hd : 2≤d) (ε K η θ χ C Q pstar ζ : ℝ)
    (hε : 0<ε) (hK : 1≤K) (hη : 0<η) (hθ0:0≤θ) (hθ1:θ<1) (hη1 : η<1-θ) (hχ : 0<χ)
    (hpstar : 0<pstar) (hζ : 0<ζ) :
    ∃ M₀ N : ℕ,1≤M₀ ∧ 1≤N ∧ ∀ (V U Γ Color : Type) (W Z : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (f : ∀ i,W i↪oV) (g : ∀ i,Z i↪U) (ρ : ∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρ i x)=π (f i x)) →
    ∀ (I T : ∀ i,Finset (W i)) (J Wrem : ∀ i,Finset (Z i)) (L : ℕ),
      (L+1:ℝ)≤(Fintype.card V:ℝ)^C →
      (∀ i≤L,T i⊆I i) → (∀ i≤L,Wrem i⊆J i) →
      (∀ i≤L,((T i).card:ℝ)≤θ*(I i).card) →
      (∀ i≤L,((Wrem i).card:ℝ)≤θ*(J i).card) →
      (∀ i≤L,(M₀:ℝ)≤(1-θ)*((I i).card:ℝ)) →
      (∀ i≤L,(M₀:ℝ)≤(1-θ)*((J i).card:ℝ)) →
      (∀ i<L,((I (i+1)).card:ℝ)≤η*(I i).card) →
      (∀ i<L,((J (i+1)).card:ℝ)≤η*(J i).card) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤K*(I i).card) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤K*(I i).card) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤K*(J i).card) →
      (∀ i≤L,∀ x,ρ i x∈I i ↔ x∈I i) →
      (∀ i≤L,∀ x,ρ i x∈T i ↔ x∈T i) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1)
      (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a : Γ) (j : Color)
      (t₀ : ℝ),(∀ u,q u a=t₀) → pstar*Fintype.card V≤t₀*Fintype.card U →
    1-2*χ-2*(Fintype.card V:ℝ)^(-Q)≤
      (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>∀ i≤L,
          let ω := rawMarkedRestrictPair (f i) (g i) z.1
          let H := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u);
          ∀ deltaR deltaV deltaU : ℝ,0≤deltaR→0≤deltaV→0≤deltaU→
          ∀ (DR : SimpleGraph (W i)) (DS : SimpleGraph (W i⊕Z i)),
            (∀ x,((DR.neighborFinset x∩(I i\T i)).card:ℝ)≤deltaR)→
            (∀ x,((((J i\Wrem i)).filter (fun u=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaV)→
            (∀ u,((((I i\T i)).filter (fun x=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaU)→
          MarkedRowsWithSpokes (P.comap (f i)) (ρ i) d h ((I i\T i)) p k
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((ε+h*ζ)*((I i\T i)).card+h*(deltaR+deltaU))
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS) ∧
          MarkedIndicesWithSpokes (ρ i) d h ((J i\Wrem i))
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((ε+h*ζ)*((J i\Wrem i)).card+h*deltaV)
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS)) := by
  have hden:0<1-θ:=by linarith
  have hK0:0≤K:=by linarith
  have hK':1≤K/(1-θ):=by
    apply (le_div_iff₀ hden).2
    linarith
  have hη':0<η/(1-θ):=div_pos hη hden
  have hη'1:η/(1-θ)<1:=vortex_sdiff_ratio_lt_one θ η hθ1 hη1
  obtain ⟨M,N,hM,hN,hbase⟩:=marked_neighbourhood_adaptive_vortex_event h d hd ε (K/(1-θ)) (η/(1-θ)) χ C Q pstar ζ
    hε hK' hη' hη'1 hχ hpstar hζ
  refine ⟨M,N,hM,hN,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ _ hn hu P π hπ f g ρ hcomm I T J Wrem L hL
    hsubI hsubJ hsmallI hsmallJ hminI hminJ hstepI hstepJ hWI hZI hWJ hI hT
  have hscaleI:=vortex_sdiff_scales W I T L θ η hθ0 hθ1 (le_of_lt hη) hsubI hsmallI hstepI
  have hscaleJ:=vortex_sdiff_scales Z J Wrem L θ η hθ0 hθ1 (le_of_lt hη) hsubJ hsmallJ hstepJ
  have hsizeI:=vortex_sdiff_size_bounds W I T L θ η K M (fun i=>(Fintype.card (W i):ℝ))
    hθ0 hθ1 (le_of_lt hη) hK0 hsubI hsmallI hstepI hminI hWI
  have hsizeIZ:=vortex_sdiff_size_bounds W I T L θ η K M (fun i=>(Fintype.card (Z i):ℝ))
    hθ0 hθ1 (le_of_lt hη) hK0 hsubI hsmallI hstepI hminI hZI
  have hsizeJ:=vortex_sdiff_size_bounds Z J Wrem L θ η K M (fun i=>(Fintype.card (W i):ℝ))
    hθ0 hθ1 (le_of_lt hη) hK0 hsubJ hsmallJ hstepJ hminJ hWJ
  have hInv:=vortex_sdiff_invariant W I T ρ L hI hT
  intro p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass
  have hAI:∀ i≤L,M≤(I i\T i).card:=by
    intro i hi
    exact_mod_cast hsizeI.1 i hi
  have hBJ:∀ i≤L,M≤(J i\Wrem i).card:=by
    intro i hi
    exact_mod_cast hsizeJ.1 i hi
  exact hbase V U Γ Color W Z hn hu P π hπ f g ρ hcomm (fun i=>I i\T i) (fun i=>J i\Wrem i) L hL
    hAI hBJ hscaleI.2 hscaleJ.2 hsizeI.2 hsizeIZ.2 hsizeJ.2 hInv
    p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass
end Oberwolfach
