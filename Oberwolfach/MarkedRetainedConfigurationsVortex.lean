module

public import Oberwolfach.MarkedLocalConfigurationVortex
public import Oberwolfach.MarkedConfigurationSpokeChanges
public import Oberwolfach.RetainedMarkedRestrictionChanges
public import Oberwolfach.RawMarkedRetentionEvent
public import Oberwolfach.PermutationInvariantImage

@[expose] public section

/-! Actual local cycle and root-omitted path counts at all fixed vortex
levels after the single global interval-retention experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_retained_configurations_vortex_event
    (r : ℕ) (hr : 1≤r) (α tstar kstar K η χ C Q pstar ζ : ℝ)
    (hα : 0<α) (hα1 : α≤1/2) (htstar : 0<tstar) (hkstar : 0<kstar)
    (hK : 1≤K) (hη : 0<η) (hη1 : η<1) (hχ : 0<χ)
    (hpstar : 0<pstar) (hζ : 0<ζ) (d : ℕ) (hd : 2≤d) :
    ∃ M₀ N : ℕ,1≤M₀ ∧ 1≤N ∧ ∀ (V U Γ Color : Type) (W Z : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (f : ∀ i,W i↪oV) (g : ∀ i,Z i↪U) (ρ : ∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρ i x)=π (f i x)) →
    ∀ (A : ∀ i,Finset (W i)) (L : ℕ),
      (L+1:ℝ)≤(Fintype.card V:ℝ)^C →
      (∀ i≤L,M₀≤(A i).card) → (∀ i≤L,M₀≤Fintype.card (Z i)) →
      (∀ i<L,((A (i+1)).card:ℝ)≤η*(A i).card) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤K*(A i).card) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤K*(A i).card) →
      (∀ i≤L,∀ x,ρ i x∈A i ↔ x∈A i) →
      (∀ i≤L,∀ x : W i,(1/2+α)*(A i).card≤(((P.comap (f i)).neighborFinset x∩A i).card:ℝ)) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1),kstar≤p → kstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a : Γ) (j : Color)
      (s₀ t₀ : ℝ),(∀ u,q u a=t₀) → (∀ u,s u j=s₀) → tstar≤s₀ → tstar≤t₀ →
      pstar*Fintype.card V≤t₀*Fintype.card U →
    1-χ-(Fintype.card V:ℝ)^(-Q)≤
      (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>∀ i≤L,MarkedLocalConfigurationsWithSpokes r (P.comap (f i)) (ρ i) d (A i)
          (markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζ)
          (markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζ)
          (rawMarkedRestrictPair (f i) (g i) z.1)
          (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) := by
  obtain ⟨m,N,hm,hN1,hret⟩ := raw_marked_retention_common_event d hd C Q pstar ζ hpstar hζ
  obtain ⟨M,hM1,hconfigs⟩ := marked_local_configurations_vortex_event r hr α tstar kstar K η χ
    hα hα1 htstar hkstar hK hη hη1 hχ d hd
  refine ⟨max m M,N,hm.trans (le_max_left _ _),hN1,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ _ hn hu P π hπ f g ρ hcomm A L hL hA hZ hstep hW hZU hInv hP p k hp hk hphys hpmin hkmin q hq hQ s hs hS a j s₀ t₀ ha hj hslo htlo hmass
  let S : Fin (L+1)→Finset V := fun i=>(A i.val).image (f i.val)
  let T : Fin (L+1)→Finset U := fun i=>Finset.univ.image (g i.val)
  have hSc (i : Fin (L+1)) : (S i).card=(A i.val).card := Finset.card_image_of_injective _ (f i.val).injective
  have hTc (i : Fin (L+1)) : (T i).card=Fintype.card (Z i.val) := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ (g i.val).injective,Finset.card_univ]
  let E := fun σ : RawMarkedOutcome V U Γ Color=>∀ i≤L,
    RawMarkedLocalConfigurations r (P.comap (f i)) (ρ i) d a j (A i)
      (markedLocalCycleCoefficient r α (tstar/2) kstar) (markedLocalPathCoefficient r α (tstar/2) kstar)
      (rawMarkedRestrictPair (f i) (g i) σ)
  have hE : 1-χ≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).probability E :=
    hconfigs V U Γ Color W Z P π hπ f g ρ hcomm A L
      (fun i hi=>(le_max_right m M).trans (hA i hi)) hstep hInv hW hZU hP
      p k hp hk hphys hpmin hkmin q hq hQ s hs hS a j s₀ t₀ ha hj hslo htlo
  have hb := hret V U Γ Color (Fin (L+1)) hn hu
    (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hL)
    π hπ p k hp hk hphys q hq hQ s hs hS a t₀ ha hmass S T
    (fun i=>permutation_invariant_image (f i.val) π (ρ i.val) (hcomm i.val) (A i.val) (hInv i.val (by omega)))
    (fun i=>by rw [hSc];exact (le_max_left m M).trans (hA i.val (by omega)))
    (fun i=>by rw [hTc];exact (le_max_left m M).trans (hZ i.val (by omega))) E χ hE
  apply hb.trans
  apply finiteLaw_probability_mono
  intro z hz i hi
  have hc := retainedMarked_restricted_col_changes (f i) (g i) π (ρ i) (hcomm i) d z.1 a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j (A i) (ζ*(A i).card) (by
      intro u
      have hh := (hz.2.2 (⟨i,by omega⟩ : Fin (L+1))).1 u
      rw [hSc] at hh
      exact hh)
  exact markedLocalConfigurations_spoke_changes r (P.comap (f i)) (ρ i) d a j (A i)
    (markedLocalCycleCoefficient r α (tstar/2) kstar) (markedLocalPathCoefficient r α (tstar/2) kstar)
    ζ (rawMarkedRestrictPair (f i) (g i) z.1) _ (hz.1 i hi) hc

end Oberwolfach
