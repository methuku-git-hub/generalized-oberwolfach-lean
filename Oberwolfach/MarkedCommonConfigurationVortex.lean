module

public import Oberwolfach.MarkedReferenceConfigurations
public import Oberwolfach.RawMarkedPairRestriction
public import Oberwolfach.VortexUniformEvents

@[expose] public section

/-! Compatible hubs, two-hub cycles and root-omitted paths on all fixed vortex
levels of one original sample. No degree centre or near-regularity
assumption is needed for these configuration counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_common_configurations_vortex_event
    (r : ℕ) (hr : 1≤r) (α sstar tstar kstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hsstar : 0<sstar) (htstar : 0<tstar) (hkstar : 0<kstar) (hω : 0<ω) :
    ∃ β : ℝ,0<β ∧ ∀ η χ : ℝ,0<η → η<1 → 0<χ → ∀ d : ℕ,∀ hd : 2≤d,
    ∃ M : ℕ,1≤M ∧ ∀ (V U Γ Color : Type) (W Z : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)],
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (f : ∀ i,W i↪oV) (g : ∀ i,Z i↪U) (ρ : ∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρ i x)=π (f i x)) →
    ∀ L : ℕ,(∀ i≤L,M≤Fintype.card (W i)) →
      (∀ i<L,(Fintype.card (W (i+1)):ℝ)≤η*Fintype.card (W i)) →
      (∀ i≤L,ω*Fintype.card (W i)≤(Fintype.card (Z i):ℝ)) →
      (∀ i≤L,Fintype.card (Z i)≤Fintype.card (W i)) →
      (∀ i≤L,∀ x : W i,(1/2+α)*Fintype.card (W i)≤((P.comap (f i)).degree x:ℝ)) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),kstar≤p → kstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (a : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u a=t₀) → (∀ u,s u j=s₀) → sstar≤s₀ → tstar≤t₀ →
    1-χ≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ i≤L,MarkedReferenceConfigurations r (P.comap (f i)) (ρ i) d a j β
        (rawMarkedRestrictPair (f i) (g i) σ)) := by
  obtain ⟨β,hβ,hconfig⟩ := marked_configurations_raw_event r hr α sstar tstar kstar ω
    hα hα1 hsstar htstar hkstar hω
  refine ⟨β,hβ,?_⟩
  intro η χ hη hη1 hχ d hd
  obtain ⟨N,hN⟩ := hconfig d hd
  let c := markedConfigurationExponent r α sstar tstar kstar ω d
  have hc : 0<c := markedConfigurationExponent_pos r α sstar tstar kstar ω d hα hsstar htstar hkstar hω
  obtain ⟨M,hM1,hM⟩ := vortex_exponential_common_event 34 c η χ (r+8) hc hη hη1 hχ
  refine ⟨max M N,hM1.trans (le_max_left _ _),?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ P π hnoshort f g ρ hcomm L hn hstep hmlo hmhi hP p k hp hk hsum hpmin hkmin q hq hQ s hs hS a j s₀ t₀ hq₀ hs₀ hslo htlo
  let μ : FiniteLaw (RawMarkedOutcome V U Γ Color) := FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)
  let Good := fun i (σ : RawMarkedOutcome V U Γ Color)=>
    MarkedReferenceConfigurations r (P.comap (f i)) (ρ i) d a j β (rawMarkedRestrictPair (f i) (g i) σ)
  apply hM (RawMarkedOutcome V U Γ Color) μ (fun i=>Fintype.card (W i)) L
    (by intro i hi;exact (le_max_left M N).trans (hn i hi)) hstep Good
  intro i hi
  let Local := fun σ : RawMarkedOutcome (W i) (Z i) Γ Color=>
    MarkedReferenceConfigurations r (P.comap (f i)) (ρ i) d a j β σ
  have hlaw := rawMarked_pair_restriction_probability (f i) (f i).injective (g i) (g i).injective
    p k hp hk hsum d hd q hq hQ s hs hS Local
  change _≤μ.probability (fun σ=>Local (rawMarkedRestrictPair (f i) (g i) σ))
  rw [hlaw]
  have hh := hN (W i) (Z i) Γ Color ((le_max_right M N).trans (hn i hi)) (hmlo i hi) (hmhi i hi)
    (P.comap (f i)) (hP i hi) (ρ i) (by
      intro x l hl hld he
      have he' := congrArg (f i) he
      rw [permutation_embedding_power (f i) π (ρ i) (hcomm i) l x] at he'
      exact hnoshort (f i x) l hl hld he') p k hp hk hsum hpmin hkmin
    (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
    (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)) a j s₀ t₀
    (fun z=>hq₀ (g i z)) (fun z=>hs₀ (g i z)) hslo htlo
  exact hh

end Oberwolfach
