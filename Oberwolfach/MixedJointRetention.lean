module

public import Oberwolfach.ColourEventMarginals

@[expose] public section

/-! Exact joint retention probabilities for prescribed, possibly distinct,
colours at the specified vertices. Neighbours avoid a set of colours; their
avoidance probabilities are not replaced by products over those colours. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def forbiddenRootColours {V C : Type*} (G : SimpleGraph V) (S : Finset V)
    (β : V → C) (u : V) : Finset C :=
  (S.filter (fun v=>G.Adj v u)).image β

theorem mem_forbiddenRootColours {V C : Type*} (G : SimpleGraph V) (S : Finset V)
    (β : V → C) (u : V) (c : C) :
    c∈forbiddenRootColours G S β u ↔ ∃ v∈S,G.Adj v u ∧ β v=c := by
  simp only [forbiddenRootColours,Finset.mem_image,Finset.mem_filter]
  aesop

theorem mixed_joint_coinRetention_probability
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
    (G : SimpleGraph V) (μ : V → FiniteLaw C)
    (a : V → C → ℝ) (ha : ∀ v c,0≤a v c ∧ a v c≤1)
    (S : Finset V) (β : V → C)
    (hproper : ∀ v∈S,∀ u∈S,G.Adj v u → β v≠β u) :
    (FiniteLaw.pi (fun u=>(μ u).withCoin (a u) (ha u))).probability
      (fun σ=>∀ v∈S,coinRetainedColour G σ v=some (β v))=
      (∏ v∈S,(μ v).mass (β v)*a v (β v))*
        ∏ u∈Finset.univ\S,(1-∑ c∈forbiddenRootColours G S β u,(μ u).mass c) := by
  classical
  let ν := fun u=>(μ u).withCoin (a u) (ha u)
  let A : V → C×Bool → Prop := fun u x=>
    if u∈S then x.1=β u ∧ x.2=true else x.1∉forbiddenRootColours G S β u
  have hevent (σ : V → C×Bool) :
      (∀ v∈S,coinRetainedColour G σ v=some (β v)) ↔ ∀ u,A u (σ u) := by
    constructor
    · intro h u
      by_cases hu : u∈S
      · obtain ⟨hc,hcoin,_⟩ := (coinRetainedColour_eq_some G σ u (β u)).mp (h u hu)
        simp [A,hu,hc,hcoin]
      · simp only [A,hu,ite_false]
        intro hc
        obtain ⟨v,hv,hvu,hc⟩ := (mem_forbiddenRootColours G S β u _).mp hc
        obtain ⟨hvc,_,hkeep⟩ := (coinRetainedColour_eq_some G σ v (β v)).mp (h v hv)
        exact hkeep u hvu (hc.symm.trans hvc.symm)
    · intro h v hv
      obtain ⟨hc,hcoin⟩ : (σ v).1=β v ∧ (σ v).2=true := by simpa [A,hv] using h v
      apply (coinRetainedColour_eq_some G σ v (β v)).mpr
      refine ⟨hc,hcoin,?_⟩
      intro u hadj
      change (σ u).1≠(σ v).1
      by_cases hu : u∈S
      · have huc : (σ u).1=β u := (show (σ u).1=β u ∧ (σ u).2=true by
          simpa [A,hu] using h u).1
        rw [huc,hc]
        exact Ne.symm (hproper v hv u hu hadj)
      · have hn : (σ u).1∉forbiddenRootColours G S β u := by simpa [A,hu] using h u
        intro he
        exact hn ((mem_forbiddenRootColours G S β u _).mpr ⟨v,hv,hadj,hc.symm.trans he.symm⟩)
  rw [finiteLaw_probability_congr (FiniteLaw.pi ν) _ _ hevent,
    finiteLaw_pi_probability_forall ν A]
  have hcoord (u : V) : (ν u).probability (A u)=
      (if u∈S then (μ u).mass (β u)*a u (β u) else 1)*
        (if u∈Finset.univ\S then 1-∑ c∈forbiddenRootColours G S β u,(μ u).mass c else 1) := by
    by_cases hu : u∈S
    · simp only [A,hu,ite_true,Finset.mem_sdiff,Finset.mem_univ,not_true_eq_false,
        and_false,ite_false,mul_one]
      exact finiteLaw_withCoin_success _ _ _ _
    · simp only [A,hu,ite_false,Finset.mem_sdiff,Finset.mem_univ,not_false_eq_true,
        and_self,ite_true,one_mul]
      exact finiteLaw_withCoin_avoid_finset _ _ _ _
  simp_rw [hcoord]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_mem,Finset.univ_inter]

end Oberwolfach
