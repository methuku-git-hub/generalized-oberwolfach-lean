module

public import Oberwolfach.CapacityPositionCorrections
public import Oberwolfach.SignedDemandNormalization

@[expose] public section

/-! Passage between directed edge occurrences and their capacity matrix.
Injectivity of the ordered endpoints is used whenever an individual matrix
entry is identified with one edge weight. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def occurrenceCapacityMatrix {V E : Type*} [Fintype E] [DecidableEq V]
    (tail head : E → V) (w : E → ℝ) (x y : V) : ℝ :=
  ∑ e,if tail e=x ∧ head e=y then w e else 0

theorem occurrenceCapacityMatrix_row {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (w : E → ℝ) (x : V) :
    (∑ y,occurrenceCapacityMatrix tail head w x y)=occurrenceSumLinear tail w x := by
  unfold occurrenceCapacityMatrix
  rw [Finset.sum_comm]
  change _=∑ e,if tail e=x then w e else 0
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : tail e=x <;> simp [h]

theorem occurrenceCapacityMatrix_col {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (w : E → ℝ) (y : V) :
    (∑ x,occurrenceCapacityMatrix tail head w x y)=occurrenceSumLinear head w y := by
  unfold occurrenceCapacityMatrix
  rw [Finset.sum_comm]
  change _=∑ e,if head e=y then w e else 0
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : head e=y <;> simp [h]

theorem occurrenceCapacityMatrix_at_edge {V E : Type*} [Fintype E] [DecidableEq V]
    (tail head : E → V) (hinj : Function.Injective (fun e => (tail e,head e)))
    (w : E → ℝ) (e : E) : occurrenceCapacityMatrix tail head w (tail e) (head e)=w e := by
  classical
  unfold occurrenceCapacityMatrix
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    have hh : ¬(tail f=tail e ∧ head f=head e) := fun h => hfe (hinj (Prod.ext h.1 h.2))
    simp only [hh,ite_false]
  · simp

theorem occurrenceCapacityMatrix_zero {V E : Type*} [Fintype E] [DecidableEq V]
    (tail head : E → V) (w : E → ℝ) (x y : V)
    (hxy : ¬∃ e,tail e=x ∧ head e=y) : occurrenceCapacityMatrix tail head w x y=0 := by
  apply Finset.sum_eq_zero
  intro e _
  exact if_neg (fun h => hxy ⟨e,h⟩)

theorem occurrenceCapacityMatrix_nonneg {V E : Type*} [Fintype E] [DecidableEq V]
    (tail head : E → V) (w : E → ℝ) (hw : ∀ e,0≤w e) (x y : V) :
    0≤occurrenceCapacityMatrix tail head w x y := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact hw e
  · exact le_rfl

theorem occurrenceCapacityMatrix_positive_bounds {V E : Type*} [Fintype E] [DecidableEq V]
    (tail head : E → V) (hinj : Function.Injective (fun e => (tail e,head e)))
    (w : E → ℝ) (a b : ℝ) (hw : ∀ e,a≤w e ∧ w e≤b) (x y : V)
    (hpos : 0<occurrenceCapacityMatrix tail head w x y) :
    a≤occurrenceCapacityMatrix tail head w x y ∧ occurrenceCapacityMatrix tail head w x y≤b := by
  by_cases h : ∃ e,tail e=x ∧ head e=y
  · obtain ⟨e,rfl,rfl⟩ := h
    rw [occurrenceCapacityMatrix_at_edge tail head hinj w e]
    exact hw e
  · rw [occurrenceCapacityMatrix_zero tail head w x y h] at hpos
    exact (lt_irrefl _ hpos).elim

theorem injective_occurrence_card_bound {V E : Type*} [Fintype V] [Fintype E]
    (tail head : E → V) (hinj : Function.Injective (fun e => (tail e,head e))) :
    Fintype.card E≤(Fintype.card V)^2 := by
  simpa only [Fintype.card_prod,pow_two] using Fintype.card_le_of_injective _ hinj

theorem injective_occurrence_degree_bound {V E : Type*} [Fintype V] [Fintype E]
    (tail head : E → V) (hinj : Function.Injective (fun e => (tail e,head e))) (v : V) :
    occurrenceDegree tail v≤(Fintype.card V : ℝ) := by
  classical
  have hi : Function.Injective (fun e : {e : E // tail e=v} => head e.val) := by
    intro e f hef
    apply Subtype.ext
    exact hinj (Prod.ext (e.property.trans f.property.symm) hef)
  have hh := Fintype.card_le_of_injective _ hi
  have he : occurrenceDegree tail v=(Fintype.card {e : E // tail e=v} : ℝ) := by
    simp only [occurrenceDegree,Finset.sum_boole,Fintype.card_subtype]
  rw [he]
  exact_mod_cast hh

end Oberwolfach
