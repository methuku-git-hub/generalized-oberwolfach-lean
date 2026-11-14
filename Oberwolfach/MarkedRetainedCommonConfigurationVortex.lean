module

public import Oberwolfach.MarkedCommonConfigurationVortex
public import Oberwolfach.MarkedCommonConfigurationSpokeChanges
public import Oberwolfach.RetainedMarkedRestrictionChanges
public import Oberwolfach.RawMarkedRetentionEvent
public import Oberwolfach.PermutationInvariantImage

@[expose] public section

/-! Compatible hubs, two-hub cycles and root-omitted common paths on all
fixed vortex levels after one global interval-retention experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_retained_common_configurations_vortex_event
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
        (fun z=>∀ i≤L,MarkedCommonConfigurationsWithSpokes r (P.comap (f i)) (ρ i) d β ζ
          (rawMarkedRestrictPair (f i) (g i) z.1)
          (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) := by
  obtain ⟨β,hβ,hconfig⟩ := marked_common_configurations_vortex_event r hr α sstar tstar kstar ω
    hα hα1 hsstar htstar hkstar hω
  refine ⟨β,hβ,?_⟩
  intro η χ C Q pstar ζ hη hη1 hχ hpstar hζ d hd
  obtain ⟨m,N,hm,hN1,hret⟩ := raw_marked_retention_common_event d hd C Q pstar ζ hpstar hζ
  obtain ⟨M,hM1,hconfigs⟩ := hconfig η χ hη hη1 hχ d hd
  refine ⟨max m M,N,hm.trans (le_max_left _ _),hN1,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ _ hn hu P π hπ f g ρ hcomm L hL hW hZ hstep hmlo hmhi hP p k hp hk hphys hpmin hkmin q hq hQ s hs hS a j s₀ t₀ ha hj hslo htlo hmass
  let S : Fin (L+1)→Finset V := fun i=>Finset.univ.image (f i.val)
  let T : Fin (L+1)→Finset U := fun i=>Finset.univ.image (g i.val)
  have hSc (i : Fin (L+1)) : (S i).card=Fintype.card (W i.val) := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ (f i.val).injective,Finset.card_univ]
  have hTc (i : Fin (L+1)) : (T i).card=Fintype.card (Z i.val) := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ (g i.val).injective,Finset.card_univ]
  let E := fun σ : RawMarkedOutcome V U Γ Color=>∀ i≤L,
    MarkedReferenceConfigurations r (P.comap (f i)) (ρ i) d a j β (rawMarkedRestrictPair (f i) (g i) σ)
  have hE : 1-χ≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).probability E :=
    hconfigs V U Γ Color W Z P π hπ f g ρ hcomm L
      (fun i hi=>(le_max_right m M).trans (hW i hi)) hstep hmlo hmhi hP
      p k hp hk hphys hpmin hkmin q hq hQ s hs hS a j s₀ t₀ ha hj hslo htlo
  have hb := hret V U Γ Color (Fin (L+1)) hn hu
    (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hL)
    π hπ p k hp hk hphys q hq hQ s hs hS a t₀ ha hmass S T
    (fun i=>permutation_invariant_image (f i.val) π (ρ i.val) (hcomm i.val) Finset.univ (by simp))
    (fun i=>by rw [hSc];exact (le_max_left m M).trans (hW i.val (by omega)))
    (fun i=>by rw [hTc];exact (le_max_left m M).trans (hZ i.val (by omega))) E χ hE
  apply hb.trans
  apply finiteLaw_probability_mono
  intro z hz i hi
  have hc := retainedMarked_restricted_col_changes (f i) (g i) π (ρ i) (hcomm i) d z.1 a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j Finset.univ (ζ*Fintype.card (W i)) (by
      intro u
      have hh := (hz.2.2 (⟨i,by omega⟩ : Fin (L+1))).1 u
      rw [hSc] at hh
      exact hh)
  have hr := retainedMarked_restricted_row_changes (f i) (g i) π (ρ i) (hcomm i) d z.1 a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j Finset.univ (ζ*Fintype.card (Z i)) (by
      intro x
      have hh := (hz.2.2 (⟨i,by omega⟩ : Fin (L+1))).2 x
      rw [hTc] at hh
      exact hh)
  have hr' : ∀ b x,(∑ u,if ¬(rawMarkedPairSpokes (ρ i) d
      (rawMarkedRestrictPair (f i) (g i) z.1) a j b x u ↔
      retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))
      then (1:ℝ) else 0)≤ζ*Fintype.card (W i) := by
    intro b x
    exact (hr b x).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hmhi i hi) hζ.le)
  exact markedCommonConfigurations_spoke_changes r (P.comap (f i)) (ρ i) d a j β ζ
    (rawMarkedRestrictPair (f i) (g i) z.1) _ (hz.1 i hi) hr' hc

end Oberwolfach
