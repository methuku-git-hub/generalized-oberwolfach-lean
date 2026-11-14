module

public import Oberwolfach.HypergraphRootColorSampling

@[expose] public section

/-! The induced colour classes have disjoint vertex sets. The root-omitted
sums coincide with their degrees at vertices of the specified colour. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    [DecidableEq V] [Nonempty C]

def hypergraphColorClass (R : E → Finset V) (σ : V → C) (c : C) : Finset E :=
  Finset.univ.filter (fun e=>∀ v∈R e,σ v=c)

theorem hypergraphColorClass_mem (R : E → Finset V) (σ : V → C) (c : C) (e : E) :
    e∈hypergraphColorClass R σ c ↔ ∀ v∈R e,σ v=c := by
  simp only [hypergraphColorClass,Finset.mem_filter,Finset.mem_univ,true_and]

theorem hypergraphColorClass_disjoint_vertices (R : E → Finset V) (σ : V → C)
    (c d : C) (hcd : c≠d) (e f : E)
    (he : e∈hypergraphColorClass R σ c) (hf : f∈hypergraphColorClass R σ d) :
    Disjoint (R e) (R f) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact hcd (((hypergraphColorClass_mem R σ c e).mp he v hv).symm.trans
    ((hypergraphColorClass_mem R σ d f).mp hf v hw))

theorem hypergraphColorClass_weight (R : E → Finset V) (w : E → ℝ) (σ : V → C) (c : C) :
    (∑ e∈hypergraphColorClass R σ c,w e)=monochromaticWeightedSum R w c σ := by
  unfold hypergraphColorClass monochromaticWeightedSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  rw [patternValue_indicator]
  split_ifs <;> simp

theorem hypergraphColorClass_degree (R : E → Finset V) (σ : V → C) (c : C) (v : V)
    (hv : σ v=c) :
    (((hypergraphColorClass R σ c).filter (fun e=>v∈R e)).card:ℝ)=
      monochromaticWeightedSum (hypergraphRootRemainder R v) (fun _=>1) c σ := by
  rw [hypergraphRootColor_present R v c σ hv,← Finset.sum_boole]
  unfold hypergraphColorClass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp only [ite_and,and_comm]
  all_goals split_ifs <;> rfl

theorem hypergraphColorClass_degree_zero (R : E → Finset V) (σ : V → C) (c : C) (v : V)
    (hv : σ v≠c) : ((hypergraphColorClass R σ c).filter (fun e=>v∈R e)).card=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hh := Finset.mem_filter.mp he
  exact hv ((hypergraphColorClass_mem R σ c e).mp hh.1 v hh.2)

end Oberwolfach
