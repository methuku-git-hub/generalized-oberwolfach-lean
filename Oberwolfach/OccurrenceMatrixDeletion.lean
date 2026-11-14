module

public import Oberwolfach.OccurrenceCapacityMatrix
public import Oberwolfach.TypedMatrixRemainders
public import Oberwolfach.DirectedCutBounds

@[expose] public section

/-! Integer matrix deletions are realised by subsets of the original edge
occurrences. The original endpoints are retained, not reconstructed. Ordered
endpoint injectivity is the precise condition that makes each entry 0 or 1. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype E] [DecidableEq V]

def occurrenceMultiplicity (tail head : E → V) (x y : V) : ℕ :=
  ∑ e,if tail e=x ∧ head e=y then 1 else 0

theorem occurrenceMultiplicity_cast (tail head : E → V) (x y : V) :
    (occurrenceMultiplicity tail head x y : ℝ)=occurrenceCapacityMatrix tail head (fun _=>1) x y := by
  simp only [occurrenceMultiplicity,occurrenceCapacityMatrix,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem occurrenceMultiplicity_at_edge (tail head : E → V)
    (hinj : Function.Injective (fun e=>(tail e,head e))) (e : E) :
    occurrenceMultiplicity tail head (tail e) (head e)=1 := by
  have hh := occurrenceCapacityMatrix_at_edge tail head hinj (fun _=>1) e
  rw [← occurrenceMultiplicity_cast] at hh
  exact_mod_cast hh

theorem occurrenceMultiplicity_zero (tail head : E → V) (x y : V)
    (hxy : ¬∃ e,tail e=x ∧ head e=y) : occurrenceMultiplicity tail head x y=0 := by
  have hh := occurrenceCapacityMatrix_zero tail head (fun _=>1) x y hxy
  rw [← occurrenceMultiplicity_cast] at hh
  exact_mod_cast hh

theorem occurrenceMultiplicity_le_one (tail head : E → V)
    (hinj : Function.Injective (fun e=>(tail e,head e))) (x y : V) :
    occurrenceMultiplicity tail head x y≤1 := by
  by_cases h : ∃ e,tail e=x ∧ head e=y
  · obtain ⟨e,rfl,rfl⟩ := h
    rw [occurrenceMultiplicity_at_edge tail head hinj]
  · rw [occurrenceMultiplicity_zero tail head x y h];omega

theorem occurrenceMultiplicity_restricted_at_edge (tail head : E → V)
    (hinj : Function.Injective (fun e=>(tail e,head e))) (keep : E → Prop) (e : E) :
    occurrenceMultiplicity (fun f : {e // keep e}=>tail f.val) (fun f=>head f.val) (tail e) (head e)=
      if keep e then 1 else 0 := by
  have hi : Function.Injective (fun f : {e // keep e}=>(tail f.val,head f.val)) := by
    intro f g hfg;apply Subtype.ext;exact hinj hfg
  by_cases hk : keep e
  · rw [if_pos hk]
    exact occurrenceMultiplicity_at_edge _ _ hi ⟨e,hk⟩
  · rw [if_neg hk]
    apply occurrenceMultiplicity_zero
    rintro ⟨f,ht,hh⟩
    exact hk ((hinj (Prod.ext ht hh)) ▸ f.property)

theorem occurrenceMultiplicity_matrix_restriction (tail head : E → V)
    (hinj : Function.Injective (fun e=>(tail e,head e))) (J : V → V → ℕ)
    (hJ : ∀ x y,J x y≤occurrenceMultiplicity tail head x y) (x y : V) :
    occurrenceMultiplicity (fun e : {e // J (tail e) (head e)=0}=>tail e.val) (fun e=>head e.val) x y=
      occurrenceMultiplicity tail head x y-J x y := by
  by_cases h : ∃ e,tail e=x ∧ head e=y
  · obtain ⟨e,rfl,rfl⟩ := h
    have hh := occurrenceMultiplicity_restricted_at_edge tail head hinj (fun f=>J (tail f) (head f)=0) e
    have hh' : occurrenceMultiplicity (fun f : {e // J (tail e) (head e)=0}=>tail f.val)
        (fun f=>head f.val) (tail e) (head e)=(if J (tail e) (head e)=0 then 1 else 0) := by
      convert hh using 1 <;> congr!
    rw [hh',occurrenceMultiplicity_at_edge tail head hinj]
    have hj := hJ (tail e) (head e)
    rw [occurrenceMultiplicity_at_edge tail head hinj] at hj
    split_ifs <;> omega
  · have hr : ¬∃ e : {e // J (tail e) (head e)=0},tail e.val=x ∧ head e.val=y := by
      rintro ⟨e,he⟩;exact h ⟨e.val,he⟩
    rw [occurrenceMultiplicity_zero _ _ x y hr,occurrenceMultiplicity_zero tail head x y h]
    simp

theorem occurrenceMultiplicity_row [Fintype V] (tail head : E → V) (x : V) :
    (∑ y,(occurrenceMultiplicity tail head x y : ℝ))=occurrenceDegree tail x := by
  simp only [occurrenceMultiplicity_cast]
  rw [occurrenceCapacityMatrix_row]
  dsimp only [occurrenceSumLinear,LinearMap.coe_mk,AddHom.coe_mk,occurrenceDegree]
  congr!

theorem occurrenceMultiplicity_col [Fintype V] (tail head : E → V) (y : V) :
    (∑ x,(occurrenceMultiplicity tail head x y : ℝ))=occurrenceDegree head y := by
  simp only [occurrenceMultiplicity_cast]
  rw [occurrenceCapacityMatrix_col]
  dsimp only [occurrenceSumLinear,LinearMap.coe_mk,AddHom.coe_mk,occurrenceDegree]
  congr!

theorem occurrence_matrix_deleted_degree (tail head : E → V)
    (hinj : Function.Injective (fun e=>(tail e,head e))) (J : V → V → ℕ)
    (hJ : ∀ x y,J x y≤occurrenceMultiplicity tail head x y) [Fintype V] (x : V) :
    (∑ e,if ¬J (tail e) (head e)=0 ∧ tail e=x then (1:ℝ) else 0)=∑ y,(J x y : ℝ) := by
  have heq (a b : V) :
      occurrenceCapacityMatrix tail head (fun e=>if J (tail e) (head e)=0 then 0 else 1) a b=(J a b : ℝ) := by
    by_cases h : ∃ e,tail e=a ∧ head e=b
    · obtain ⟨e,rfl,rfl⟩ := h
      rw [occurrenceCapacityMatrix_at_edge tail head hinj]
      have hj := hJ (tail e) (head e)
      rw [occurrenceMultiplicity_at_edge tail head hinj] at hj
      by_cases hz : J (tail e) (head e)=0
      · simp only [hz,ite_true,Nat.cast_zero]
      · have hh : J (tail e) (head e)=1 := by omega
        simp [hh]
    · rw [occurrenceCapacityMatrix_zero tail head _ a b h]
      have hj := hJ a b
      rw [occurrenceMultiplicity_zero tail head a b h] at hj
      have hz : J a b=0 := by omega
      simp only [hz,Nat.cast_zero]
  simp_rw [← heq x]
  rw [occurrenceCapacityMatrix_row]
  change _=∑ e,if tail e=x then (if J (tail e) (head e)=0 then 0 else 1) else 0
  apply Finset.sum_congr rfl
  intro e _
  by_cases hz : J (tail e) (head e)=0 <;> by_cases hx : tail e=x <;> simp [hz,hx]

theorem occurrence_matrix_deleted_indegree (tail head : E → V)
    (hinj : Function.Injective (fun e=>(tail e,head e))) (J : V → V → ℕ)
    (hJ : ∀ x y,J x y≤occurrenceMultiplicity tail head x y) [Fintype V] (y : V) :
    (∑ e,if ¬J (tail e) (head e)=0 ∧ head e=y then (1:ℝ) else 0)=∑ x,(J x y : ℝ) := by
  have hi : Function.Injective (fun e=>(head e,tail e)) := by
    intro e f hef;exact hinj (Prod.ext (congrArg Prod.snd hef) (congrArg Prod.fst hef))
  have hj (x y : V) : J y x≤occurrenceMultiplicity head tail x y := by
    convert hJ y x using 1 <;> simp only [occurrenceMultiplicity,and_comm] <;> congr!
  have hh := occurrence_matrix_deleted_degree head tail hi (fun x y=>J y x) hj y
  convert hh using 1 <;> congr!

theorem occurrence_matrix_cut (tail head : E → V) (S T : Finset V) :
    matrixCut (occurrenceMultiplicity tail head) S T=
      (Finset.univ.filter (fun e=>tail e∈S ∧ head e∈T)).card := by
  rw [Finset.card_filter]
  unfold matrixCut occurrenceMultiplicity
  simp_rw [Finset.sum_comm (s:=T) (t:=Finset.univ)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have he (x y : V) : (if tail e=x ∧ head e=y then (1:ℕ) else 0)=
      (if x=tail e then (if y=head e then 1 else 0) else 0) := by
    by_cases hx : x=tail e <;> by_cases hy : y=head e <;> simp_all [eq_comm]
  simp only [he]
  by_cases hx : tail e∈S <;> by_cases hy : head e∈T <;> simp [hx,hy]

theorem occurrence_matrix_cut_deletion [Fintype V] (tail head : E → V)
    (hinj : Function.Injective (fun e=>(tail e,head e))) (J : V → V → ℕ)
    (hJ : ∀ x y,J x y≤occurrenceMultiplicity tail head x y) (d : ℝ)
    (hrow : ∀ x,(∑ y,(J x y:ℝ))≤d) (hcol : ∀ y,(∑ x,(J x y:ℝ))≤d)
    (S T : Finset V) :
    ((Finset.univ.filter (fun e=>tail e∈S ∧ head e∈T)).card:ℝ)-d*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e : {e // J (tail e) (head e)=0}=>tail e.val∈S ∧ head e.val∈T)).card:ℝ) := by
  have hp (x y : V) : occurrenceMultiplicity tail head x y≤
      occurrenceMultiplicity (fun e : {e // J (tail e) (head e)=0}=>tail e.val) (fun e=>head e.val) x y+J x y := by
    rw [occurrenceMultiplicity_matrix_restriction tail head hinj J hJ]
    omega
  have hh := matrixCut_loss_bound (occurrenceMultiplicity tail head)
    (occurrenceMultiplicity (fun e : {e // J (tail e) (head e)=0}=>tail e.val) (fun e=>head e.val)) J hp
    (by intro x;simpa only [Nat.cast_sum] using hrow x)
    (by intro y;simpa only [Nat.cast_sum] using hcol y) S T
  simpa only [occurrence_matrix_cut] using hh

end Oberwolfach
