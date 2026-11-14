module

public import Oberwolfach.ColourRetentionCoins

@[expose] public section

/-! Joint retention probabilities for pairwise nonadjacent vertices.
All roots and all avoiding neighbours belong to the same product space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def setNeighbours {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun u=>∃ v∈S,G.Adj v u)

theorem independentSet_disjoint_neighbours {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V)
    (hS : ∀ u∈S,∀ v∈S,¬G.Adj u v) : Disjoint S (setNeighbours G S) := by
  apply Finset.disjoint_left.mpr
  intro u hu hn
  obtain ⟨v,hv,hvu⟩ := (Finset.mem_filter.mp hn).2
  exact hS v hv u hu hvu

theorem joint_coinRetention_probability
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
    (G : SimpleGraph V) (μ : V → FiniteLaw C)
    (a : V → C → ℝ) (ha : ∀ v c,0≤a v c ∧ a v c≤1)
    (S : Finset V) (hS : ∀ u∈S,∀ v∈S,¬G.Adj u v) (c : C) :
    (FiniteLaw.pi (fun u=>(μ u).withCoin (a u) (ha u))).probability
      (fun σ=>∀ v∈S,coinRetainedColour G σ v=some c)=
      (∏ v∈S,(μ v).mass c*a v c)*
        ∏ u∈setNeighbours G S,(1-(μ u).mass c) := by
  classical
  let ν := fun u=>(μ u).withCoin (a u) (ha u)
  let N := setNeighbours G S
  have hdis : Disjoint S N := independentSet_disjoint_neighbours G S hS
  let A : V → C×Bool → Prop := fun u x=>
    if u∈S then x.1=c ∧ x.2=true else if u∈N then x.1≠c else True
  have hevent (σ : V → C×Bool) :
      (∀ v∈S,coinRetainedColour G σ v=some c) ↔ ∀ u,A u (σ u) := by
    constructor
    · intro h u
      by_cases hu : u∈S
      · obtain ⟨hc,hcoin,_⟩ := (coinRetainedColour_eq_some G σ u c).mp (h u hu)
        simp [A,hu,hc,hcoin]
      · by_cases hn : u∈N
        · obtain ⟨v,hv,hvu⟩ := (Finset.mem_filter.mp hn).2
          obtain ⟨hc,_,hkeep⟩ := (coinRetainedColour_eq_some G σ v c).mp (h v hv)
          simpa [A,hu,hn,hc] using hkeep u hvu
        · simp [A,hu,hn]
    · intro h v hv
      obtain ⟨hc,hcoin⟩ : (σ v).1=c ∧ (σ v).2=true := by simpa [A,hv] using h v
      apply (coinRetainedColour_eq_some G σ v c).mpr
      refine ⟨hc,hcoin,?_⟩
      intro u hadj
      have hn : u∈N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hv,hadj⟩
      have hu : u∉S := fun hu=>Finset.disjoint_left.mp hdis hu hn
      simpa [A,hu,hn,hc] using h u
  rw [finiteLaw_probability_congr (FiniteLaw.pi ν) _ _ hevent,
    finiteLaw_pi_probability_forall ν A]
  have hcoord (u : V) : (ν u).probability (A u)=
      (if u∈S then (μ u).mass c*a u c else 1)*
        (if u∈N then 1-(μ u).mass c else 1) := by
    by_cases hs : u∈S
    · have hn : u∉N := fun hn=>Finset.disjoint_left.mp hdis hs hn
      simp only [A,hs,ite_true,hn,ite_false,mul_one]
      exact finiteLaw_withCoin_success _ _ _ _
    · by_cases hn : u∈N
      · simp only [A,hs,ite_false,hn,ite_true,one_mul]
        exact finiteLaw_withCoin_not_colour _ _ _ _
      · simp only [A,hs,hn,ite_false,one_mul]
        exact finiteLaw_probability_true _
  simp_rw [hcoord]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_mem,Finset.univ_inter]
  rfl

end Oberwolfach
