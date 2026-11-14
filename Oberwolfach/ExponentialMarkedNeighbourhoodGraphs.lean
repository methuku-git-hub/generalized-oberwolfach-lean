module

public import Oberwolfach.ExponentialMarkedNeighbourhoods
public import Oberwolfach.PermutationNeighbourCounts

@[expose] public section

/-! Fixed-domain count estimates expressed as degrees into the actual
random common neighbourhood and its permutation image. All ambient roots
are controlled on the same event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawMarkedNeighbourhood_exponential_graph_event
    (ε : ℝ) (hε : 0<ε) (k d : ℕ) (hk : 0<k) (hd : 2≤d) :
    ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      0<Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V)
      (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    1-12*(Fintype.card V:ℝ)^(k+1)*Real.exp (-(2*ε^2/((4*(d:ℝ)+3)^2*k))*Fintype.card V)≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ (b : Bool) (u : Fin k→U),Function.Injective u →
          let T := Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))
          let a := if b then t₀ else s₀
          (|(T.card:ℝ)-a^k*Fintype.card V|<ε*Fintype.card V) ∧
          (∀ x : V,|((P.neighborFinset x∩T).card:ℝ)-a^k*P.degree x|<ε*Fintype.card V) ∧
          (∀ x : V,|((P.neighborFinset x∩T.image π).card:ℝ)-a^k*P.degree x|<ε*Fintype.card V)) := by
  intro V U Γ Color _ _ _ _ _ _ hn hmhi P π q hq hQ s hs hS g j s₀ t₀ hg hj hnoshort
  have hh := rawMarkedNeighbourhood_exponential_ambient_event ε hε k d hk hd V U Γ Color hn hmhi P π q hq hQ s hs hS g j s₀ t₀ hg hj hnoshort
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ b u hu
  let T := Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))
  refine ⟨?_,?_,?_⟩
  · simpa only [markedReferenceDomain,Finset.card_univ] using hσ b u hu none
  · intro x
    have hfilter : (P.neighborFinset x).filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))=
        P.neighborFinset x∩T := by ext v;simp only [T,Finset.mem_filter,Finset.mem_inter,Finset.mem_univ,true_and]
    have hi := hσ b u hu (some (Sum.inl x))
    simpa only [markedReferenceDomain,hfilter,SimpleGraph.card_neighborFinset_eq_degree] using hi
  · intro x
    have hfilter : (markedReferenceDomain P π (some (Sum.inr x))).filter
        (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))=
        T.filter (fun v=>P.Adj x (π v)) := by
      ext v
      simp only [markedReferenceDomain,T,Finset.mem_filter,Finset.mem_univ,true_and,and_comm]
    have hi := hσ b u hu (some (Sum.inr x))
    rw [hfilter,permutation_neighbour_filter_card] at hi
    simpa only [markedReferenceDomain,permutation_neighbour_domain_card] using hi

end Oberwolfach
