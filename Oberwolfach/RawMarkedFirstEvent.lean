module

public import Oberwolfach.GoodPlacementEvents
public import Oberwolfach.RawMarkedDenseNeighbourhoods
public import Oberwolfach.RawMarkedSpokeDisjointness
public import Oberwolfach.RawMarkedHubProbability

@[expose] public section

/-! The first exposure in the marked configuration argument: all compatible
hub counts and both dense spoke-intersection classes hold on one event.
The class disjointness is deterministic, and every graph-neighbourhood
estimate ranges over the full vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawMarked_first_event
    (m : ℕ) (α sstar tstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hsstar : 0<sstar) (htstar : 0<tstar) (hω : 0<ω)
    (d q₀ : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
    ∀ (π : Equiv.Perm V)
      (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) → sstar≤s₀ → tstar≤t₀ →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>
          (∀ C : Fin (m+1)→V,PermutationSeparated π (3*d) C →
            (ω*tstar*sstar^m/2)*Fintype.card V≤
              ((potentialMarkedHubs (rawMarkedSpokes π d σ g j) C).card:ℝ)) ∧
          (∀ (u : Fin 2→U),Function.Injective u →
            let T := fun b : Bool=>Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))
            Disjoint (T false) (T true) ∧ Disjoint (T false) ((T true).image π) ∧
            ∀ b : Bool,
              ((min sstar tstar)^2/2*Fintype.card V≤((T b).card:ℝ)) ∧
              (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩T b).card:ℝ)) ∧
              (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩(T b).image π).card:ℝ)))) := by
  let pstar := min sstar tstar
  have hpstar : 0<pstar := lt_min hsstar htstar
  obtain ⟨N₁,hN₁⟩ := rawMarkedHubs_uniform_probability_explicit m sstar tstar ω hsstar htstar hω d (q₀+1) hd
  obtain ⟨N₂,hN₂⟩ := rawMarkedNeighbourhood_dense_event α pstar hα hα1 hpstar d (q₀+1) hd
  refine ⟨max 2 (max N₁ N₂),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P hP π q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo hnoshort
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hh := hN₁ V U Γ Color (by omega) hmlo hmhi π q hq hQ s hs hS g j
    (by intro u;rw [hg];exact htlo) (by intro u;rw [hj];exact hslo) hnoshort
  have hdense := hN₂ V U Γ Color (by omega) hmhi P hP π q hq hQ s hs hS g j s₀ t₀ hg hj
    ((min_le_left _ _).trans hslo) ((min_le_right _ _).trans htlo) hnoshort
  have hjoint := finiteLaw_good_intersection μ
    (fun σ=>∀ C : Fin (m+1)→V,PermutationSeparated π (3*d) C →
      (ω*tstar*sstar^m/2)*Fintype.card V≤((potentialMarkedHubs (rawMarkedSpokes π d σ g j) C).card:ℝ))
    _ (1/(n:ℝ)^(q₀+1)) hdense
  have hbase := (sub_le_sub_right hh (1/(n:ℝ)^(q₀+1))).trans hjoint
  have hsum := scaled_inverse_power_le n q₀ hn 2 (by exact_mod_cast (show 2≤n by dsimp [n];omega))
  have hbound : 1-1/(n:ℝ)^q₀≤(1-1/(n:ℝ)^(q₀+1))-1/(n:ℝ)^(q₀+1) := by
    convert sub_le_sub_left hsum 1 using 1 <;> ring
  apply (hbound.trans hbase).trans
  apply finiteLaw_probability_mono
  intro σ hσ
  refine ⟨hσ.1,?_⟩
  intro u hu
  have hdisj := rawMarkedSpokeClasses_disjoint π d (by omega) σ g j u
  exact ⟨hdisj.1,hdisj.2,fun b=>hσ.2 b u hu⟩

end Oberwolfach
