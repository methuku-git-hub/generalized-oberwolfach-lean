module

public import Oberwolfach.RawMarkedSeedLoadEvent
public import Oberwolfach.MarkedLoadFailureBounds
public import Oberwolfach.RawMarkedPairRestriction
public import Oberwolfach.VortexUniformEvents

@[expose] public section

/-! Root-omitted local spoke loads for fixed domain-specific coefficients.
All outer hubs are tested; each weight function is retained on its own
inner vertex domain and its normalization is not recomputed after exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option quotPrecheck false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def RawMarkedLocalSpokeLoads (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (D p k s₀ : ℝ) (weight : (Fin (m+1)→V)→ℝ) (g : Γ) (j : Color)
    (η : ℝ) (σ : RawMarkedOutcome V U Γ Color) : Prop :=
  let seed := fun W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
    (fun (_ : V) (_ : U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
  ∀ a : Bool×V×U,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ)
    (rawMarkedPairSpokes π d σ g j) (Sum.inr a)-1|≤η

theorem rawMarkedLocalSpokeLoads_exponential_event
    (P : SimpleGraph V) (π : Equiv.Perm V) (p k : ℝ) (hp : 0<p) (hk : 0<k) (hsum : 2*p+2*k≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (m : ℕ) (hm : 3≤m) (g : Γ) (j : Color)
    (s₀ t₀ D τ A B : ℝ) (hs₀ : 0<s₀) (hD : 0<D) (ht : t₀=s₀/m)
    (hq₀ : ∀ u,q u g=t₀) (hs₀' : ∀ u,s u j=s₀)
    (weight : (Fin (m+1)→V)→ℝ)
    (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (hn : 0<Fintype.card V) (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (pstar : ℝ) (hpstar : 0<pstar) (hpp : pstar≤p) (hpk : pstar≤k) (hps : pstar≤s₀)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀≤1) (hB : 0<B)
    (K : ℝ) (hu : (Fintype.card U:ℝ)≤K*Fintype.card V) (ε : ℝ) (hε : 0<ε) :
    1-4*K*(Fintype.card V:ℝ)^2*Real.exp (-markedLoadExponent m d (2*B/pstar^(2*m+1)) ε*Fintype.card V)≤
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hsum d hd q hq hQ s hs hS)).probability
      (RawMarkedLocalSpokeLoads P π d m D p k s₀ weight g j (τ+ε)) := by
  have hh := rawMarkedSeed_external_spoke_event P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
    m hm g j s₀ t₀ D τ A B hs₀ hD ht hq₀ hs₀' weight hw hn hDlo hDhi pstar hpstar hpp hpk hps hp1 hk1 hs1 hB ε hε
  have herr := marked_load_failure_bound m d (2*B/pstar^(2*m+1)) ε (Fintype.card V)
    (Fintype.card (Bool×V×U)) (2*K) (by exact_mod_cast hn) (marked_external_spoke_domain_card K hu)
  have he : 2*(2*K)=4*K := by ring
  rw [he] at herr
  exact (sub_le_sub_left herr 1).trans hh

theorem marked_local_spoke_loads_vortex_event
    (m d : ℕ) (hm : 3≤m) (hd : 2≤d) (B pstar ε K η χ : ℝ)
    (hB : 0<B) (hpstar : 0<pstar) (hε : 0<ε) (hη : 0<η) (hη1 : η<1) (hχ : 0<χ) :
    ∃ M₀ : ℕ,1≤M₀ ∧ ∀ (V U Γ Color : Type) (W Z : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)],
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (f : ∀ i,W i↪oV) (g : ∀ i,Z i↪U) (ρ : ∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρ i x)=π (f i x)) →
    ∀ L : ℕ,(∀ i≤L,M₀≤Fintype.card (W i)) →
      (∀ i<L,(Fintype.card (W (i+1)):ℝ)≤η*Fintype.card (W i)) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤K*Fintype.card (W i)) →
    ∀ (D : ℕ→ℝ) (τ A : ℝ),
      (∀ i≤L,(Fintype.card (W i):ℝ)/2≤D i) → (∀ i≤L,D i≤2*Fintype.card (W i)) →
    ∀ weight : ∀ i,(Fin (m+1)→W i)→ℝ,
      (∀ i≤L,SuccessorSequenceWeightConditions (P.comap (f i)) (ρ i) (3*d) (D i) τ A B (weight i)) →
    ∀ (p k s₀ : ℝ) (hp : 0<p) (hk : 0<k) (hsum : 2*p+2*k≤1),
      pstar≤p → pstar≤k → pstar≤s₀ → p≤1 → k≤1 → s₀≤1 →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (a : Γ) (j : Color),(∀ u,q u a=s₀/m) → (∀ u,s u j=s₀) →
    1-χ≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ i≤L,RawMarkedLocalSpokeLoads (P.comap (f i)) (ρ i) d m (D i) p k s₀ (weight i) a j (τ+ε)
        (rawMarkedRestrictPair (f i) (g i) σ)) := by
  let c := markedLoadExponent m d (2*B/pstar^(2*m+1)) ε
  have hc : 0<c := markedLoadExponent_pos m d _ ε (by positivity) hε
  obtain ⟨M₀,hM1,hM⟩ := vortex_exponential_common_event (4*K) c η χ 2 hc hη hη1 hχ
  refine ⟨M₀,hM1,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ P π hnoshort f g ρ hcomm L hn hstep hZ D τ A hDlo hDhi weight hw p k s₀ hp hk hsum hpp hpk hps hp1 hk1 hs1 q hq hQ s hs hS a j hq₀ hs₀
  let μ : FiniteLaw (RawMarkedOutcome V U Γ Color) :=
    FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hsum d hd q hq hQ s hs hS)
  let Good := fun i (σ : RawMarkedOutcome V U Γ Color)=>
    RawMarkedLocalSpokeLoads (P.comap (f i)) (ρ i) d m (D i) p k s₀ (weight i) a j (τ+ε)
      (rawMarkedRestrictPair (f i) (g i) σ)
  apply hM (RawMarkedOutcome V U Γ Color) μ (fun i=>Fintype.card (W i)) L hn hstep Good
  intro i hi
  let Local := fun σ : RawMarkedOutcome (W i) (Z i) Γ Color=>
    RawMarkedLocalSpokeLoads (P.comap (f i)) (ρ i) d m (D i) p k s₀ (weight i) a j (τ+ε) σ
  have hlaw := rawMarked_pair_restriction_probability (f i) (f i).injective (g i) (g i).injective
    p k hp.le hk.le hsum d hd q hq hQ s hs hS Local
  change _≤μ.probability (fun σ=>Local (rawMarkedRestrictPair (f i) (g i) σ))
  rw [hlaw]
  have hni : 0<Fintype.card (W i) := lt_of_lt_of_le (by omega : 0<M₀) (hn i hi)
  have hni' : (0:ℝ)<Fintype.card (W i) := by exact_mod_cast hni
  apply rawMarkedLocalSpokeLoads_exponential_event (P.comap (f i)) (ρ i) p k hp hk hsum d hd
    (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
    (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)) _
    m hm a j s₀ (s₀/m) (D i) τ A B (hpstar.trans_le hps) ((half_pos hni').trans_le (hDlo i hi))
    rfl (fun z=>hq₀ (g i z)) (fun z=>hs₀ (g i z)) (weight i) (hw i hi) hni (hDlo i hi) (hDhi i hi)
    pstar hpstar hpp hpk hps hp1 hk1 hs1 hB K (hZ i hi) ε hε
  intro x l hl hld he
  have hh := congrArg (f i) he
  rw [permutation_embedding_power (f i) π (ρ i) (hcomm i) l x] at hh
  exact hnoshort (f i x) l hl hld hh

end Oberwolfach
