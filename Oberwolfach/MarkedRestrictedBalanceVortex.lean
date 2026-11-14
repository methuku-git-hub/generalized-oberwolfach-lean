module

public import Oberwolfach.UniformMarkedRestrictedBalance
public import Oberwolfach.RawMarkedPairRestriction
public import Oberwolfach.VortexUniformEvents

@[expose] public section

/-! Simultaneous restricted balance on fixed vortex domains, including
all outer roots. The supplied local scales may exceed the restriction sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawMarkedRestrictedBalance_empty {V U Γ Color : Type}
    [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (g : Γ) (j : Color)
    (η : ℝ) (hη : 0≤η) (σ : RawMarkedOutcome V U Γ Color) :
    RawMarkedRestrictedBalance P π d m g j ∅ ∅ η σ := by
  simp [RawMarkedRestrictedBalance,markedRestrictedDegree,rawMarkedRestrictedSpokeRow,
    rawMarkedRestrictedSpokeCol,hη]

theorem marked_restricted_balance_vortex_event
    (m d : ℕ) (hd : 2≤d) (ε K η χ : ℝ) (hε : 0<ε) (hK : 1≤K)
    (hη : 0<η) (hη1 : η<1) (hχ : 0<χ) :
    ∃ M₀ : ℕ,1≤M₀ ∧ ∀ (V U Γ Color : Type) (W Z : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)],
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (f : ∀ i,W i↪oV) (g : ∀ i,Z i↪U) (ρ : ∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρ i x)=π (f i x)) →
    ∀ (A : ∀ i,Finset (W i)) (B : ∀ i,Finset (Z i)) (M : ℕ→ℕ) (L : ℕ),
      (∀ i≤L,M₀≤M i) → (∀ i<L,(M (i+1):ℝ)≤η*M i) →
      (∀ i≤L,(A i).Nonempty) → (∀ i≤L,(B i).Nonempty) →
      (∀ i≤L,(A i).card≤M i) → (∀ i≤L,(B i).card≤M i) →
      (∀ i≤L,∀ x,ρ i x∈A i ↔ x∈A i) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤K*M i) → (∀ i≤L,(Fintype.card (Z i):ℝ)≤K*M i) →
    ∀ (D : ℕ→ℝ) (δP : ℝ),0≤δP → δP≤ε/4 →
      (∀ i≤L,∀ x : W i,|(((P.comap (f i)).neighborFinset x∩A i).card:ℝ)-D i|≤δP*M i) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (a : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u a=t₀) → (∀ u,s u j=s₀) →
      (∀ i≤L,p*D i=s₀*(B i).card) → (∀ i≤L,k*D i=t₀*(B i).card) → s₀=(m:ℝ)*t₀ →
    1-χ≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ i≤L,RawMarkedRestrictedBalance (P.comap (f i)) (ρ i) d m a j (A i) (B i) (ε*M i)
          (rawMarkedRestrictPair (f i) (g i) σ)) := by
  obtain ⟨N,hN⟩ := marked_restricted_balance_uniform_event m d hd ε K hε hK
  let c := markedRestrictedBalanceExponent m d ε K
  have hc : 0<c := markedRestrictedBalanceExponent_pos m d ε K hε (by linarith)
  obtain ⟨M₀,hM1,hM⟩ := vortex_exponential_common_event (16*K) c η χ 1 hc hη hη1 hχ
  refine ⟨max M₀ N,hM1.trans (le_max_left _ _),?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ P π hnoshort f g ρ hcomm A B M L hn hstep hA hB hAM hBM hInv hW hZ D δP hδP hδε hP p k hp hk hsum q hq hQ s hs hS a j s₀ t₀ hq₀ hs₀ hD0 hDK hratio
  let μ : FiniteLaw (RawMarkedOutcome V U Γ Color) :=
    FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)
  let Good := fun i (σ : RawMarkedOutcome V U Γ Color)=>
    RawMarkedRestrictedBalance (P.comap (f i)) (ρ i) d m a j (A i) (B i) (ε*M i)
      (rawMarkedRestrictPair (f i) (g i) σ)
  apply hM (RawMarkedOutcome V U Γ Color) μ M L
    (by intro i hi;exact (le_max_left M₀ N).trans (hn i hi)) hstep Good
  intro i hi
  let Local := fun σ : RawMarkedOutcome (W i) (Z i) Γ Color=>
    RawMarkedRestrictedBalance (P.comap (f i)) (ρ i) d m a j (A i) (B i) (ε*M i) σ
  have hlaw := rawMarked_pair_restriction_probability (f i) (f i).injective (g i) (g i).injective
    p k hp hk hsum d hd q hq hQ s hs hS Local
  change _≤μ.probability (fun σ=>Local (rawMarkedRestrictPair (f i) (g i) σ))
  rw [hlaw]
  simp only [pow_one]
  apply hN (W i) (Z i) Γ Color (M i) ((le_max_right M₀ N).trans (hn i hi)) (hW i hi) (hZ i hi)
    (P.comap (f i)) (ρ i) (A i) (B i) (hA i hi) (hB i hi) (hAM i hi) (hBM i hi) (hInv i hi)
    (D i) δP hδP hδε (hP i hi) p k hp hk hsum
    (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
    (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)) _ a j s₀ t₀
    (fun z=>hq₀ (g i z)) (fun z=>hs₀ (g i z)) (hD0 i hi) (hDK i hi) hratio
  intro x l hl hld he
  have hh := congrArg (f i) he
  rw [permutation_embedding_power (f i) π (ρ i) (hcomm i) l x] at hh
  exact hnoshort (f i x) l hl hld hh

end Oberwolfach
