module

public import Oberwolfach.CommonEvents
public import Oberwolfach.FiniteUniform

@[expose] public section

/-! Selecting one colour class in each vertex-disjoint part of a hypergraph.
The resulting matching and its weight sums are represented explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {E I C V : Type*} [Fintype E] [Fintype I] [DecidableEq E] [DecidableEq I]
    [DecidableEq C] [DecidableEq V]

def colorClassSelection (part : E → I) (color : E → C) (σ : I → C) : Finset E :=
  Finset.univ.filter (fun e=>color e=σ (part e))

def colorClassWeight (part : E → I) (color : E → C) (w : E → ℝ) (i : I) (c : C) : ℝ :=
  ∑ e,if part e=i ∧ color e=c then w e else 0

theorem colorClassSelection_matching (R : E → Finset V) (part : E → I) (color : E → C)
    (hparts : ∀ e f,part e≠part f → Disjoint (R e) (R f))
    (hcolor : ∀ e f,e≠f → part e=part f → color e=color f → Disjoint (R e) (R f))
    (σ : I → C) : ∀ e∈colorClassSelection part color σ,∀ f∈colorClassSelection part color σ,e≠f → Disjoint (R e) (R f) := by
  intro e he f hf hef
  have he' : color e=σ (part e) := (Finset.mem_filter.mp he).2
  have hf' : color f=σ (part f) := (Finset.mem_filter.mp hf).2
  by_cases hp : part e=part f
  · exact hcolor e f hef hp (he'.trans ((congrArg σ hp).trans hf'.symm))
  · exact hparts e f hp

theorem colorClassSelection_weight (part : E → I) (color : E → C) (w : E → ℝ) (σ : I → C) :
    (∑ e∈colorClassSelection part color σ,w e)=∑ i,colorClassWeight part color w i (σ i) := by
  unfold colorClassSelection colorClassWeight
  rw [Finset.sum_filter,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_eq_single (part e)]
  · simp
  · intro i _ hi
    simp only [Ne.symm hi,false_and,ite_false]
  · simp

theorem colorClassWeight_nonneg (part : E → I) (color : E → C) (w : E → ℝ)
    (hw : ∀ e,0≤w e) (i : I) (c : C) : 0≤colorClassWeight part color w i c := by
  unfold colorClassWeight
  apply Finset.sum_nonneg
  intro e _
  by_cases h : part e=i ∧ color e=c
  · rw [if_pos h];exact hw e
  · simp only [if_neg h,le_refl]

theorem colorClassWeight_total [Fintype C] (part : E → I) (color : E → C) (w : E → ℝ) :
    (∑ i,∑ c,colorClassWeight part color w i c)=∑ e,w e := by
  unfold colorClassWeight
  calc
    _ = ∑ i,∑ e,∑ c,if part e=i ∧ color e=c then w e else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ e,∑ i,∑ c,if part e=i ∧ color e=c then w e else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [ite_and]
      simp

theorem colorClassWeight_coordinate_change (part : E → I) (color : E → C)
    (w : E → ℝ) (hw : ∀ e,0≤w e) (B : I → ℝ)
    (hB : ∀ i c,colorClassWeight part color w i c≤B i)
    (i : I) (σ τ : I → C) (hστ : ∀ j,j≠i → σ j=τ j) :
    |(∑ j,colorClassWeight part color w j (σ j))-(∑ j,colorClassWeight part color w j (τ j))|≤B i := by
  have he : (∑ j,colorClassWeight part color w j (σ j))-(∑ j,colorClassWeight part color w j (τ j))=
      colorClassWeight part color w i (σ i)-colorClassWeight part color w i (τ i) := by
    rw [← Finset.sum_sub_distrib,Finset.sum_eq_single i]
    · intro j _ hji;rw [hστ j hji,sub_self]
    · simp
  rw [he,abs_le]
  constructor
  · linarith [colorClassWeight_nonneg part color w hw i (σ i),hB i (τ i)]
  · linarith [colorClassWeight_nonneg part color w hw i (τ i),hB i (σ i)]

end Oberwolfach
