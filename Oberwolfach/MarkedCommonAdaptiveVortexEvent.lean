module

public import Oberwolfach.MarkedRetainedCommonConfigurationVortex
public import Oberwolfach.MarkedCommonConfigurationsAfterPhysicalDeletion

@[expose] public section

/-! One retained event controls common configurations after every later
physical deletion on every fixed domain. Deletions may depend on the whole
outcome; the event and its probability do not depend on their choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_common_adaptive_vortex_event
    (r : ℕ) (hr : 1≤r) (α sstar tstar kstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hsstar : 0<sstar) (htstar : 0<tstar) (hkstar : 0<kstar) (hω : 0<ω) :
    ∃ β : ℝ,0<β ∧ ∀ η χ C Q pstar ζ : ℝ,0<η → η<1 → 0<χ → 0<pstar → 0<ζ →
    ∀ d : ℕ,∀ hd : 2≤d,
    ∃ M₀ N : ℕ,1≤M₀ ∧ 1≤N ∧ ∀ (V U Γ Color : Type) (W Z : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (f : ∀ i,W i↪oV) (g : ∀ i,Z i↪U) (ρ : ∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρ i x)=π (f i x)) →
    ∀ L : ℕ,(L+1:ℝ)≤(Fintype.card V:ℝ)^C →
      (∀ i≤L,M₀≤Fintype.card (W i)) → (∀ i≤L,M₀≤Fintype.card (Z i)) →
      (∀ i<L,(Fintype.card (W (i+1)):ℝ)≤η*Fintype.card (W i)) →
      (∀ i≤L,ω*Fintype.card (W i)≤(Fintype.card (Z i):ℝ)) →
      (∀ i≤L,Fintype.card (Z i)≤Fintype.card (W i)) →
      (∀ i≤L,∀ x : W i,(1/2+α)*Fintype.card (W i)≤((P.comap (f i)).degree x:ℝ)) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1),kstar≤p → kstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a : Γ) (j : Color)
      (s₀ t₀ : ℝ),(∀ u,q u a=t₀) → (∀ u,s u j=s₀) → sstar≤s₀ → tstar≤t₀ →
      pstar*Fintype.card V≤t₀*Fintype.card U →
    1-χ-(Fintype.card V:ℝ)^(-Q)≤
      (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>∀ i≤L,∀ δ : ℝ,0≤δ→
          ∀ (DR : SimpleGraph (W i)) (DS : SimpleGraph (W i⊕Z i)),
          (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
          MarkedCommonConfigurationsWithSpokes r (P.comap (f i)) (ρ i) d β (ζ+4*δ/Fintype.card (W i))
            (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset)
            (markedDeletePhysicalSpokes
              (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
                (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a))
                  z.2 a j b (f i x) (g i u)) DS)) := by
  obtain ⟨β,hβ,hbase⟩ := marked_retained_common_configurations_vortex_event r hr α sstar tstar kstar ω
    hα hα1 hsstar htstar hkstar hω
  refine ⟨β,hβ,?_⟩
  intro η χ C Q pstar ζ hη hη1 hχ hpstar hζ d hd
  obtain ⟨M,N,hM,hN,hbase⟩ := hbase η χ C Q pstar ζ hη hη1 hχ hpstar hζ d hd
  refine ⟨M,N,hM,hN,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ _ hn hu P π hπ f g ρ hcomm L hL hW hZ hstep hmlo hmhi hP
    p k hp hk hphys hpmin hkmin q hq hQ s hs hS a j s₀ t₀ ha hj hslo htlo hmass
  have he := hbase V U Γ Color W Z hn hu P π hπ f g ρ hcomm L hL hW hZ hstep hmlo hmhi hP
    p k hp hk hphys hpmin hkmin q hq hQ s hs hS a j s₀ t₀ ha hj hslo htlo hmass
  apply he.trans
  apply finiteLaw_probability_mono
  intro z hz i hi δ hδ DR DS hDR hDS
  exact marked_common_configurations_after_physical_deletion r (P.comap (f i)) (ρ i) d β ζ δ hδ
    (lt_of_lt_of_le (by omega) (hW i hi)) _ _ DR DS hDR hDS (hz i hi)

end Oberwolfach
