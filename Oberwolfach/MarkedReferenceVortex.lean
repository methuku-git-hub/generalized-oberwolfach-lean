module

public import Oberwolfach.MarkedReferenceCommonEvent
public import Oberwolfach.RawMarkedPairRestriction
public import Oberwolfach.VortexUniformEvents

@[expose] public section

/-! Reference estimates at every fixed vortex level of one marked sample.
All vertex/hub domains and permutations are supplied before exposure. The
terminal order bound is independent of the initial order and number of levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reference_vortex_event
    (r : ℕ) (hr : 1≤r) (γ sstar tstar kstar κ : ℝ) (hγ : 0<γ) (hγ1 : γ≤1/2)
    (hsstar : 0<sstar) (htstar : 0<tstar) (htstar1 : tstar≤1) (horder : tstar≤sstar)
    (hkstar : 0<kstar) (hκ : 0<κ) :
    ∃ β : ℝ,0<β ∧ ∀ ε δ η χ : ℝ,0<ε → 0<δ → 0<η → η<1 → 0<χ → ∀ d : ℕ,∀ hd : 2≤d,
    ∃ M : ℕ,1≤M ∧ ∀ (V U Γ Color : Type) (W Z : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)],
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (f : ∀ i,W i↪oV) (g : ∀ i,Z i↪U) (ρ : ∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρ i x)=π (f i x)) →
    ∀ L : ℕ,(∀ i≤L,M≤Fintype.card (W i)) →
      (∀ i<L,(Fintype.card (W (i+1)):ℝ)≤η*Fintype.card (W i)) →
      (∀ i≤L,κ*Fintype.card (W i)≤(Fintype.card (Z i):ℝ)) →
      (∀ i≤L,Fintype.card (Z i)≤Fintype.card (W i)) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),kstar≤p → kstar≤k →
    ∀ (D : ℕ→ℝ) (δP : ℝ),0≤δP → δP≤ε/4 →
      (∀ i≤L,∀ x : W i,|((P.comap (f i)).degree x:ℝ)-D i|≤δP*Fintype.card (W i)) →
      (∀ i≤L,∀ x : W i,(1/2+γ)*Fintype.card (W i)≤((P.comap (f i)).degree x:ℝ)) →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (a : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u a=t₀) → (∀ u,s u j=s₀) → sstar≤s₀ → tstar≤t₀ →
    1-χ≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ i≤L,
        (MarkedReferenceStatistics (P.comap (f i)) (ρ i) d a j (D i) ε δ γ p k s₀ t₀
          (rawMarkedRestrictPair (f i) (g i) σ) ∧
        MarkedReferenceCutFamilies (P.comap (f i)) (ρ i) d a j γ p k tstar
          (rawMarkedRestrictPair (f i) (g i) σ)) ∧
        MarkedReferenceConfigurations r (P.comap (f i)) (ρ i) d a j β
          (rawMarkedRestrictPair (f i) (g i) σ)) := by
  obtain ⟨β,hβ,hCommon⟩ := marked_reference_common_event r hr γ sstar tstar kstar κ
    hγ hγ1 hsstar htstar htstar1 horder hkstar hκ
  refine ⟨β,hβ,?_⟩
  intro ε δ η χ hε hδ hη hη1 hχ d hd
  obtain ⟨N,hN1,hN⟩ := hCommon ε δ hε hδ d hd
  let c := markedReferenceCommonExponent r ε δ γ sstar tstar kstar κ d
  have hc : 0<c := markedReferenceCommonExponent_pos r ε δ γ sstar tstar kstar κ d
    hε hδ hγ hsstar htstar hkstar hκ
  obtain ⟨M,hM1,hM⟩ := vortex_exponential_common_event 106 c η χ (r+8) hc hη hη1 hχ
  refine ⟨max M N,hM1.trans (le_max_left _ _),?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ P π hnoshort f g ρ hcomm L hn hstep hmlo hmhi p k hp hk hsum hpmin hkmin D δP hδP hδε hPreg hP q hq hQ s hs hS a j s₀ t₀ hq₀ hs₀ hslo htlo
  let μ : FiniteLaw (RawMarkedOutcome V U Γ Color) :=
    FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)
  let Good := fun i (σ : RawMarkedOutcome V U Γ Color)=>
    (MarkedReferenceStatistics (P.comap (f i)) (ρ i) d a j (D i) ε δ γ p k s₀ t₀
      (rawMarkedRestrictPair (f i) (g i) σ) ∧
    MarkedReferenceCutFamilies (P.comap (f i)) (ρ i) d a j γ p k tstar
      (rawMarkedRestrictPair (f i) (g i) σ)) ∧
    MarkedReferenceConfigurations r (P.comap (f i)) (ρ i) d a j β
      (rawMarkedRestrictPair (f i) (g i) σ)
  apply hM (RawMarkedOutcome V U Γ Color) μ (fun i=>Fintype.card (W i)) L
    (by intro i hi;exact (le_max_left M N).trans (hn i hi)) hstep Good
  intro i hi
  let Local := fun σ : RawMarkedOutcome (W i) (Z i) Γ Color=>
    (MarkedReferenceStatistics (P.comap (f i)) (ρ i) d a j (D i) ε δ γ p k s₀ t₀ σ ∧
      MarkedReferenceCutFamilies (P.comap (f i)) (ρ i) d a j γ p k tstar σ) ∧
      MarkedReferenceConfigurations r (P.comap (f i)) (ρ i) d a j β σ
  have hlaw := rawMarked_pair_restriction_probability (f i) (f i).injective (g i) (g i).injective
    p k hp hk hsum d hd q hq hQ s hs hS Local
  change _≤μ.probability (fun σ=>Local (rawMarkedRestrictPair (f i) (g i) σ))
  rw [hlaw]
  apply hN (W i) (Z i) Γ Color ((le_max_right M N).trans (hn i hi)) (hmlo i hi) (hmhi i hi)
    (P.comap (f i)) (ρ i) _ p k hp hk hsum hpmin hkmin (D i) δP hδP hδε (hPreg i hi) (hP i hi)
    (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
    (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)) a j s₀ t₀
    (fun z=>hq₀ (g i z)) (fun z=>hs₀ (g i z)) hslo htlo
  intro x l hl hld he
  have hh := congrArg (f i) he
  rw [permutation_embedding_power (f i) π (ρ i) (hcomm i) l x] at hh
  exact hnoshort (f i x) l hl hld hh

end Oberwolfach
