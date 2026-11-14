module

public import Oberwolfach.SuccessorWeightFamilies
public import Oberwolfach.MarkedPackingLoadVortex

@[expose] public section

/-! Construct the packing coefficient functions from parent graph hypotheses
and then realize their rim and root-omitted spoke loads on one raw sample.
Weights are chosen before the actual sampling marginals; the near-regularity
tolerance precedes the separation parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option quotPrecheck false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_packing_load_realization
    (k₀ m : ℕ) (hlen : m+1=(k₀+2)*2)
    (β τ pstar ε K η χ : ℝ) (hβ : 0<β) (hτ : 0<τ) (hpstar : 0<pstar)
    (hε : 0<ε) (hη : 0<η) (hη1 : η<1) (hχ : 0<χ) :
    ∃ δ : ℝ,0<δ ∧ ∀ d : ℕ,∀ hd : 2≤d,∃ M₀ : ℕ,1≤M₀ ∧
    ∀ (V U Γ Color : Type) (W Z H : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,Fintype (H i)]
      [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)] [∀ i,DecidableEq (H i)],
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (f : ∀ i,W i↪oV) (g : ∀ i,Z i↪U) (b : ∀ i,H i↪Z i) (ρ : ∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρ i x)=π (f i x)) →
    ∀ L : ℕ,(∀ i≤L,M₀≤Fintype.card (W i)) →
      (∀ i<L,(Fintype.card (W (i+1)):ℝ)≤η*Fintype.card (W i)) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤K*Fintype.card (W i)) →
      (∀ i≤L,Fintype.card (H i)≤Fintype.card (W i)) →
    ∀ D : ℕ→ℝ,(∀ i≤L,(Fintype.card (W i):ℝ)/2≤D i) →
      (∀ i≤L,D i≤2*Fintype.card (W i)) →
      (∀ i≤L,∀ v,|((P.comap (f i)).degree v:ℝ)-D i|≤δ*Fintype.card (W i)) →
      (∀ i≤L,∀ v,(successorCycleRatio k₀+β)*Fintype.card (W i)≤((P.comap (f i)).degree v:ℝ)) →
    ∃ weight : ∀ i,(Fin (m+1)→W i)→ℝ,
      (∀ i≤L,SuccessorSequenceWeightConditions (P.comap (f i)) (ρ i) (3*d) (D i) τ
        (successorWeightLower k₀ β) (successorWeightUpper k₀ β) (weight i)) ∧
    ∀ (p k s₀ : ℝ) (hp : 0<p) (hk : 0<k) (hsum : 2*p+2*k≤1),
      pstar≤p → pstar≤k → pstar≤s₀ → p≤1 → k≤1 → s₀≤1 →
      (∀ i≤L,(Fintype.card (H i):ℝ)*(s₀/m)=D i*k) →
      (∀ i≤L,(Fintype.card (H i):ℝ)*(s₀/m)*m=D i*p) →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (a : Γ) (j : Color),(∀ u,q u a=s₀/m) → (∀ u,s u j=s₀) →
    (∀ i≤L,∀ C : Fin (m+1)→W i,
      SuccessorSequenceValid (P.comap (f i)) (ρ i) C → PermutationSeparated (ρ i) (3*d) C →
      (successorWeightLower k₀ β/2)/(Fintype.card (W i):ℝ)^m≤weight i C/(D i*p^m*k*s₀^m) ∧
      weight i C/(D i*p^m*k*s₀^m)≤(2*successorWeightUpper k₀ β/pstar^(2*m+1))/(Fintype.card (W i):ℝ)^m) ∧
    1-χ≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ i≤L,RawMarkedPackingLoads (P.comap (f i)) (ρ i) d m (D i) p k s₀ (weight i) a j
        (b i) (fun z=>q (g i z)) (fun z=>s (g i z)) (τ+ε)
        (rawMarkedRestrictPair (f i) (g i) σ)) := by
  have hm : 3≤m := by omega
  obtain ⟨hA,hB⟩ := successorWeightConstants_pos k₀ β hβ
  obtain ⟨δ,hδ,hfamilies⟩ := successor_sequence_weight_families k₀ m hlen β τ hβ hτ
  refine ⟨δ,hδ,?_⟩
  intro d hd
  obtain ⟨N,hN1,hN⟩ := hfamilies (3*d)
  obtain ⟨M,hM1,hM⟩ := marked_packing_loads_vortex_event m d hm hd (successorWeightUpper k₀ β)
    pstar ε K η χ hB hpstar hε hη hη1 hχ
  refine ⟨max N M,hN1.trans (le_max_left _ _),?_⟩
  intro V U Γ Color W Z H _ _ _ _ _ _ _ _ _ _ _ _ P π hnoshort f g b ρ hcomm L hn hstep hZ hH D hDlo hDhi hnear hmin
  obtain ⟨weight,hw⟩ := hN W (fun i=>P.comap (f i)) ρ D L
    (fun i hi=>(le_max_left N M).trans (hn i hi)) hDlo hDhi hnear hmin
  refine ⟨weight,hw,?_⟩
  intro p k s₀ hp hk hsum hpp hpk hps hp1 hk1 hs1 hmarked hord q hq hQ s hs hS a j hq₀ hs₀
  constructor
  · intro i hi C hvalid hsep
    have hni : 0<Fintype.card (W i) := by have hh:=hn i hi;omega
    exact ⟨successor_seed_positive_lower (hw i hi) (by omega) hni (hDlo i hi) (hDhi i hi)
      p k s₀ pstar hpstar hpp hpk hps hp1 hk1 hs1 hA.le hB.le C hvalid hsep,
      (successor_seed_nonneg_upper (hw i hi) (by omega) hni (hDlo i hi) (hDhi i hi)
      p k s₀ pstar hpstar hpp hpk hps hp1 hk1 hs1 hB.le C).2⟩
  · exact hM V U Γ Color W Z H P π hnoshort f g b ρ hcomm L
      (fun i hi=>(le_max_right N M).trans (hn i hi)) hstep hZ hH D τ (successorWeightLower k₀ β)
      hDlo hDhi weight hw p k s₀ hp hk hsum hpp hpk hps hp1 hk1 hs1 hmarked hord q hq hQ s hs hS a j hq₀ hs₀

end Oberwolfach
