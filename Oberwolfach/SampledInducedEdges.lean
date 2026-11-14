module

public import Oberwolfach.SampledInducedDensity
public import Oberwolfach.PairSampleScale

@[expose] public section

/-! Exact edge probabilities in the independent vertex/edge sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_prod_map_fst {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) : (μ.prod ν).map Prod.fst=μ := by
  apply finiteLaw_ext
  intro ω
  simp only [FiniteLaw.map,FiniteLaw.prod,Fintype.sum_prod_type]
  have hh (x : Ω) : (∑ y,if x=ω then μ.mass x*ν.mass y else 0)=
      if x=ω then μ.mass x else 0 := by
    by_cases hx : x=ω
    · simp only [hx,ite_true,← Finset.mul_sum,ν.total,mul_one]
    · simp [hx]
  simp only [hh,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem sampledInducedGraph_edge_probability {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} [Nonempty (FixedSubset V m)] (hm : m≤Fintype.card V)
    (G : SimpleGraph V) (μ : Sym2 V → FiniteLaw Bool) (u v : V) (huv : G.Adj u v) :
    ((FiniteLaw.uniform (FixedSubset V m)).prod (FiniteLaw.pi μ)).probability
      (fun z => (sampledInducedGraph G z).Adj u v)=
      pairSampleProbability (Fintype.card V) m*(μ s(u,v)).mass true := by
  rw [finiteLaw_prod_probability_slices (FiniteLaw.uniform (FixedSubset V m)) (FiniteLaw.pi μ)
    (fun S σ => (sampledInducedGraph G (S,σ)).Adj u v)]
  have hp (S : FixedSubset V m) : (FiniteLaw.pi μ).probability
      (fun σ => (sampledInducedGraph G (S,σ)).Adj u v)=
      if u∈S.val ∧ v∈S.val then (μ s(u,v)).mass true else 0 := by
    by_cases hS : u∈S.val ∧ v∈S.val
    · have he : (fun σ => (sampledInducedGraph G (S,σ)).Adj u v)=
          (fun σ => σ s(u,v)=true) := by
        funext σ
        apply propext
        simp only [sampledInducedGraph,spanningRestriction_adj,retainedGraph,huv,true_and,hS.1,hS.2,and_true]
      rw [he,finiteLaw_pi_coordinate_probability,if_pos hS]
    · have he : (fun σ => (sampledInducedGraph G (S,σ)).Adj u v)=(fun _ => False) := by
        funext σ
        apply propext
        simp only [sampledInducedGraph,spanningRestriction_adj,retainedGraph,huv,true_and]
        tauto
      rw [he,finiteLaw_probability_false,if_neg hS]
  simp only [hp]
  calc
    _ = (FiniteLaw.uniform (FixedSubset V m)).probability
        (fun S => u∈S.val ∧ v∈S.val)*(μ s(u,v)).mass true := by
      unfold FiniteLaw.probability
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> simp
    _ = _ := by rw [fixedSubset_pair_probability hm u v huv.ne]

end Oberwolfach
