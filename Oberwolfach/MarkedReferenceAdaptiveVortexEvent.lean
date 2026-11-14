module

public import Oberwolfach.MarkedReferenceVortex
public import Oberwolfach.MarkedReferenceAfterPhysicalDeletion
public import Oberwolfach.RawMarkedRetention

@[expose] public section

/-! One original retained experiment supplies reference estimates for every
later rim deletion on every fixed vortex domain. The deletion may depend on
both exposures. No union bound over deletion choices is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reference_adaptive_vortex_event
    (r : ℕ) (hr : 1≤r) (γ sstar tstar kstar κ : ℝ) (hγ : 0<γ) (hγ1 : γ≤1/2)
    (hsstar : 0<sstar) (htstar : 0<tstar) (htstar1 : tstar≤1) (horder : tstar≤sstar)
    (hkstar : 0<kstar) (hκ : 0<κ) :
    ∃ β : ℝ,0<β ∧ ∀ ε δ η χ : ℝ,0<ε → 0<δ → 0<η → η<1 → 0<χ → ∀ d : ℕ,∀ hd : 2≤d,
    ∃ M : ℕ,1≤M ∧ ∀ (V U Γ Color : Type) (W Z : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
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
    1-χ≤(rawMarkedRetentionLaw π d hd a p k hp hk hsum q hq hQ s hs hS).probability
      (fun z=>∀ i≤L,
        MarkedReferenceConfigurations r (P.comap (f i)) (ρ i) d a j β
          (rawMarkedRestrictPair (f i) (g i) z.1) ∧
        ∀ ζ : ℝ,0≤ζ→2*ζ≤(3/4)*γ*p^2→ζ≤γ*min p k/8→
        ∀ DR : SimpleGraph (W i),(∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card (W i))→
        MarkedReferenceStatistics (P.comap (f i)) (ρ i) d a j (D i) (ε+ζ) δ (γ/2) p k s₀ t₀
          (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset) ∧
        MarkedReferenceCutFamilies (P.comap (f i)) (ρ i) d a j (γ/2) p k tstar
          (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset)) := by
  obtain ⟨β,hβ,hraw⟩ := marked_reference_vortex_event r hr γ sstar tstar kstar κ
    hγ hγ1 hsstar htstar htstar1 horder hkstar hκ
  refine ⟨β,hβ,?_⟩
  intro ε δ η χ hε hδ hη hη1 hχ d hd
  obtain ⟨M,hM,hraw⟩ := hraw ε δ η χ hε hδ hη hη1 hχ d hd
  refine ⟨M,hM,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ _ P π hnoshort f g ρ hcomm L hn hstep hmlo hmhi
    p k hp hk hsum hpmin hkmin D δP hδP hδε hPreg hP q hq hQ s hs hS a j s₀ t₀ hq₀ hs₀ hslo htlo
  let E := fun σ : RawMarkedOutcome V U Γ Color=>∀ i≤L,
    (MarkedReferenceStatistics (P.comap (f i)) (ρ i) d a j (D i) ε δ γ p k s₀ t₀
      (rawMarkedRestrictPair (f i) (g i) σ) ∧
    MarkedReferenceCutFamilies (P.comap (f i)) (ρ i) d a j γ p k tstar
      (rawMarkedRestrictPair (f i) (g i) σ)) ∧
    MarkedReferenceConfigurations r (P.comap (f i)) (ρ i) d a j β
      (rawMarkedRestrictPair (f i) (g i) σ)
  have he : 1-χ≤(rawMarkedRetentionLaw π d hd a p k hp hk hsum q hq hQ s hs hS).probability (fun z=>E z.1) := by
    rw [rawMarkedRetentionLaw_raw_projection]
    exact hraw V U Γ Color W Z P π hnoshort f g ρ hcomm L hn hstep hmlo hmhi
      p k hp hk hsum hpmin hkmin D δP hδP hδε hPreg hP q hq hQ s hs hS a j s₀ t₀ hq₀ hs₀ hslo htlo
  apply he.trans
  apply finiteLaw_probability_mono
  intro z hz i hi
  obtain ⟨⟨hstats,hcuts⟩,hconfigs⟩ := hz i hi
  refine ⟨hconfigs,?_⟩
  intro ζ hζ hmstat hmcut DR hDR
  constructor
  · apply marked_reference_statistics_after_physical_deletion _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hDR _ hstats
    nlinarith only [hmstat]
  · apply marked_reference_cuts_after_physical_deletion _ _ _ _ _ _ _ _ _ _ _ (by linarith only [hγ]) hζ _ _ _ hDR hcuts
    intro mark
    have hm : min p k≤(if mark then k else p) := by cases mark;exact min_le_left _ _;exact min_le_right _ _
    have hh := mul_le_mul_of_nonneg_left hm hγ.le
    nlinarith only [hmcut,hh]

end Oberwolfach
