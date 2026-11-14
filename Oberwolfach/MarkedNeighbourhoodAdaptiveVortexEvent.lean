module

public import Oberwolfach.MarkedRetainedRowsVortex
public import Oberwolfach.MarkedRetainedIndicesVortex
public import Oberwolfach.MarkedNeighbourhoodDeletionOnDomain

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

theorem marked_neighbourhood_adaptive_vortex_event
    (h d : ℕ) (hd : 2≤d) (ε K η χ C Q pstar ζ : ℝ)
    (hε : 0<ε) (hK : 1≤K) (hη : 0<η) (hη1 : η<1) (hχ : 0<χ)
    (hpstar : 0<pstar) (hζ : 0<ζ) :
    ∃ M₀ N : ℕ,1≤M₀ ∧ 1≤N ∧ ∀ (V U Γ Color : Type) (W Z : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (f : ∀ i,W i↪oV) (g : ∀ i,Z i↪U) (ρ : ∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρ i x)=π (f i x)) →
    ∀ (A : ∀ i,Finset (W i)) (B : ∀ i,Finset (Z i)) (L : ℕ),
      (L+1:ℝ)≤(Fintype.card V:ℝ)^C →
      (∀ i≤L,M₀≤(A i).card) → (∀ i≤L,M₀≤(B i).card) →
      (∀ i<L,((A (i+1)).card:ℝ)≤η*(A i).card) →
      (∀ i<L,((B (i+1)).card:ℝ)≤η*(B i).card) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤K*(A i).card) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤K*(A i).card) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤K*(B i).card) →
      (∀ i≤L,∀ x,ρ i x∈A i ↔ x∈A i) →
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
            (∀ x,((DR.neighborFinset x∩A i).card:ℝ)≤deltaR)→
            (∀ x,(((B i).filter (fun u=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaV)→
            (∀ u,(((A i).filter (fun x=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaU)→
          MarkedRowsWithSpokes (P.comap (f i)) (ρ i) d h (A i) p k
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((ε+h*ζ)*(A i).card+h*(deltaR+deltaU))
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS) ∧
          MarkedIndicesWithSpokes (ρ i) d h (B i)
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((ε+h*ζ)*(B i).card+h*deltaV)
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS)) := by
  obtain ⟨Mr,Nr,hMr,hNr,hr⟩ := marked_retained_rows_vortex_event h d hd ε K η χ C Q pstar ζ
    hε hK hη hη1 hχ hpstar hζ
  obtain ⟨Mi,Ni,hMi,hNi,hi⟩ := marked_retained_indices_vortex_event h d hd ε K η χ C Q pstar ζ
    hε hK hη hη1 hχ hpstar hζ
  refine ⟨max Mr Mi,max Nr Ni,hMr.trans (le_max_left _ _),hNr.trans (le_max_left _ _),?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ _ hn hu P π hπ f g ρ hcomm A B L hL hA hB hstepA hstepB hWA hZA hWB hInv
    p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass
  have hZ (i) (hi : i≤L) : max Mr Mi≤Fintype.card (Z i) := (hB i hi).trans (Finset.card_le_univ _)
  have hW (i) (hi : i≤L) : max Mr Mi≤Fintype.card (W i) := (hA i hi).trans (Finset.card_le_univ _)
  have hrows := hr V U Γ Color W Z ((le_max_left _ _).trans hn) hu P π hπ f g ρ hcomm A L hL
    (fun i hi=>(le_max_left _ _).trans (hA i hi)) (fun i hi=>(le_max_left _ _).trans (hZ i hi))
    hstepA hWA hZA hInv p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass
  have hindices := hi V U Γ Color W Z ((le_max_right _ _).trans hn) hu π hπ f g ρ hcomm B L hL
    (fun i hi=>(le_max_right _ _).trans (hB i hi)) (fun i hi=>(le_max_right _ _).trans (hW i hi))
    hstepB hWB p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass
  let μ := rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS
  have hind := hindices
  rw [show 1-χ-(Fintype.card V:ℝ)^(-Q)=1-(χ+(Fintype.card V:ℝ)^(-Q)) by ring] at hind
  have hjoint := (sub_le_sub_right hrows (χ+(Fintype.card V:ℝ)^(-Q))).trans
    (finiteLaw_good_intersection μ _ _ (χ+(Fintype.card V:ℝ)^(-Q)) hind)
  have hb := hjoint
  rw [show (1-χ-(Fintype.card V:ℝ)^(-Q))-(χ+(Fintype.card V:ℝ)^(-Q))=1-2*χ-2*(Fintype.card V:ℝ)^(-Q) by ring] at hb
  apply hb.trans
  apply finiteLaw_probability_mono
  intro z hz i hi ω H deltaR deltaV deltaU hR hV hU DR DS hrim hrow hcol
  exact marked_neighbourhoods_after_deletion_on_domain (P.comap (f i)) (ρ i) d h (A i) (B i) (hInv i hi)
    p k (fun u=>q (g i u)) (fun u=>s (g i u)) a j
    ((ε+h*ζ)*(A i).card) ((ε+h*ζ)*(B i).card) deltaR deltaV deltaU hR hV hU ω H
    (hz.1 i hi) (hz.2 i hi) DR DS hrim hrow hcol

end Oberwolfach
