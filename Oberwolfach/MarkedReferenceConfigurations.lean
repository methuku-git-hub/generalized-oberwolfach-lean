module

public import Oberwolfach.ExponentialRawMarkedConfigurations

@[expose] public section

/-! The complete configuration event on the same dependent raw-coordinate
space used for degrees, cuts and root-omitted loads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def MarkedReferenceConfigurations (r : ℕ) (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (g : Γ) (j : Color) (β : ℝ) (σ : RawMarkedOutcome V U Γ Color) : Prop :=
  (∀ C : Fin (r+5)→V,PermutationSeparated π (3*d) C →
    32*β*Fintype.card V≤((potentialMarkedHubs (rawMarkedPairSpokes π d σ g j) C).card:ℝ)) ∧
  (∀ u : Fin 2→U,Function.Injective u →
    16*β*(Fintype.card V:ℝ)^(r+5)≤
      (Fintype.card (SampledCommonMarkedCycle P π d (r+4)
        (fun e=>σ (Sum.inr e)) (fun e=>σ (Sum.inl e)) g j u):ℝ)) ∧
  (∀ v v' : V,v≠v' → ∀ u : Fin 2→U,Function.Injective u → ∀ b : Bool,
    16*β*(Fintype.card V:ℝ)^(r+4)≤
      (Fintype.card (SampledCommonMarkedPath P π d (r+3) b v v'
        (fun e=>σ (Sum.inr e)) (fun e=>σ (Sum.inl e)) g j u):ℝ))

theorem marked_configurations_raw_event
    (r : ℕ) (hr : 1≤r) (α sstar tstar kstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hsstar : 0<sstar) (htstar : 0<tstar) (hkstar : 0<kstar) (hω : 0<ω) :
    ∃ β : ℝ,0<β ∧ ∀ d : ℕ,∀ hd : 2≤d,∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
    ∀ (π : Equiv.Perm V),(∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),kstar≤p → kstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j₀ : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j₀=s₀) → sstar≤s₀ → tstar≤t₀ →
    1-34*(Fintype.card V:ℝ)^(r+8)*Real.exp (-markedConfigurationExponent r α sstar tstar kstar ω d*Fintype.card V)≤
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (MarkedReferenceConfigurations r P π d g j₀ β) := by
  obtain ⟨β,hβ,hβevent⟩ := rawMarked_configurations_exponential_event r hr α sstar tstar kstar ω
    hα hα1 hsstar htstar hkstar hω
  refine ⟨β,hβ,?_⟩
  intro d hd
  obtain ⟨N,hN⟩ := hβevent d hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hmlo hmhi P hP π hnoshort p k hp hk hsum hpmin hkmin q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  have hprob := hN V U Γ Color hn hmlo hmhi P hP π hnoshort p k hp hk hsum hpmin hkmin
    q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  have heq : (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (MarkedReferenceConfigurations r P π d g j β)=
    ((FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).prod
      (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum))).probability (fun z=>
      (∀ C : Fin (r+5)→V,PermutationSeparated π (3*d) C →
        32*β*Fintype.card V≤((potentialMarkedHubs (rawMarkedSpokes π d z.1 g j) C).card:ℝ)) ∧
      (∀ u : Fin 2→U,Function.Injective u →
        16*β*(Fintype.card V:ℝ)^(r+5)≤(Fintype.card (SampledCommonMarkedCycle P π d (r+4) z.1 z.2 g j u):ℝ)) ∧
      (∀ v v' : V,v≠v' → ∀ u : Fin 2→U,Function.Injective u → ∀ b : Bool,
        16*β*(Fintype.card V:ℝ)^(r+4)≤(Fintype.card (SampledCommonMarkedPath P π d (r+3) b v v' z.1 z.2 g j u):ℝ))) :=
    finiteLaw_pi_sum_probability (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)
      (fun σ τ=>
      (∀ C : Fin (r+5)→V,PermutationSeparated π (3*d) C →
        32*β*Fintype.card V≤((potentialMarkedHubs (rawMarkedSpokes π d σ g j) C).card:ℝ)) ∧
      (∀ u : Fin 2→U,Function.Injective u →
        16*β*(Fintype.card V:ℝ)^(r+5)≤(Fintype.card (SampledCommonMarkedCycle P π d (r+4) σ τ g j u):ℝ)) ∧
      (∀ v v' : V,v≠v' → ∀ u : Fin 2→U,Function.Injective u → ∀ b : Bool,
        16*β*(Fintype.card V:ℝ)^(r+4)≤(Fintype.card (SampledCommonMarkedPath P π d (r+3) b v v' σ τ g j u):ℝ)))
  rw [heq]
  exact hprob

end Oberwolfach
