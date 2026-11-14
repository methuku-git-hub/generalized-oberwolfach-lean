module

public import Oberwolfach.OccurrenceMatrixDeletion
public import Oberwolfach.MarkedHostBalance

@[expose] public section

/-! The four integer correction matrices give a host with the original
edge occurrences and endpoint maps. Spoke relations are restricted pointwise.
The resulting exact degree identities are those used by the marked weight
correction theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*}

def relationMultiplicity (H : V → U → Prop) (v : V) (u : U) : ℕ := if H v u then 1 else 0

theorem relationMultiplicity_cast (H : V → U → Prop) (v : V) (u : U) :
    (relationMultiplicity H v u : ℝ)=(if H v u then 1 else 0) := by
  simp only [relationMultiplicity,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem relationMultiplicity_remainder (H : V → U → Prop) (L : V → U → ℕ)
    (hL : ∀ v u,L v u≤relationMultiplicity H v u) (v : V) (u : U) :
    relationMultiplicity (fun v u=>H v u ∧ L v u=0) v u=relationMultiplicity H v u-L v u := by
  have hl := hL v u
  by_cases h : H v u
  · simp only [relationMultiplicity,h,ite_true,true_and] at hl ⊢
    split_ifs <;> omega
  · simp only [relationMultiplicity,h,ite_false,false_and,Nat.zero_sub]

theorem relation_matrix_deleted_entry (H : V → U → Prop) (L : V → U → ℕ)
    (hL : ∀ v u,L v u≤relationMultiplicity H v u) (v : V) (u : U) :
    (if H v u ∧ ¬(H v u ∧ L v u=0) then (1:ℝ) else 0)=(L v u : ℝ) := by
  have hl := hL v u
  by_cases h : H v u
  · simp only [relationMultiplicity,h,ite_true] at hl
    by_cases hz : L v u=0
    · simp [h,hz]
    · have hone : L v u=1 := by omega
      simp [h,hone]
  · have hz : L v u=0 := by simpa only [relationMultiplicity,h,ite_false,Nat.le_zero] using hl
    simp [h,hz]

theorem occurrenceDegree_sum [Fintype E] [Fintype K] (f : E → V) (g : K → V) (v : V) :
    occurrenceDegree (Sum.elim f g) v=occurrenceDegree f v+occurrenceDegree g v := by
  simp only [occurrenceDegree,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]

theorem typed_matrix_balanced_occurrence_degrees [Fintype V] [Fintype U]
    [Fintype E] [Fintype K] [DecidableEq V]
    (q : ℕ) (tail head : E → V) (ktail khead : K → V) (H₀ Hₖ : V → U → Prop)
    (hb : TypedMatrixBalanced q (occurrenceMultiplicity tail head) (occurrenceMultiplicity ktail khead)
      (relationMultiplicity H₀) (relationMultiplicity Hₖ)) :
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=occurrenceDegree (Sum.elim head khead) v) ∧
    (∀ v,occurrenceDegree khead v=∑ u,if Hₖ v u then (1:ℝ) else 0) ∧
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if Hₖ v u then (1:ℝ) else 0)) ∧
    (∀ u,(∑ v,if H₀ v u then (1:ℝ) else 0)=(q:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0)) := by
  have hout (v : V) : occurrenceDegree (Sum.elim tail ktail) v=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if Hₖ v u then (1:ℝ) else 0) := by
    have hh := congrArg (fun k : ℕ=>(k:ℝ)) (hb.1 v)
    simp only [Nat.cast_add,Nat.cast_sum,occurrenceMultiplicity_row,relationMultiplicity_cast] at hh
    simpa only [occurrenceDegree_sum] using hh
  have hin (v : V) : occurrenceDegree (Sum.elim head khead) v=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if Hₖ v u then (1:ℝ) else 0) := by
    have hh := congrArg (fun k : ℕ=>(k:ℝ)) (hb.2.1 v)
    simp only [Nat.cast_add,Nat.cast_sum,occurrenceMultiplicity_col,relationMultiplicity_cast] at hh
    simpa only [occurrenceDegree_sum] using hh
  refine ⟨fun v=>(hout v).trans (hin v).symm,?_,hout,?_⟩
  · intro v
    have hh := congrArg (fun k : ℕ=>(k:ℝ)) (hb.2.2.1 v)
    simpa only [Nat.cast_sum,occurrenceMultiplicity_col,relationMultiplicity_cast] using hh
  · intro u
    have hh := congrArg (fun k : ℕ=>(k:ℝ)) (hb.2.2.2 u)
    simpa only [Nat.cast_sum,Nat.cast_mul,relationMultiplicity_cast] using hh

theorem typed_matrix_remainder_realized [Fintype V] [Fintype U]
    [Fintype E] [Fintype K] [DecidableEq V]
    (q : ℕ) (tail head : E → V) (ktail khead : K → V)
    (hinj : Function.Injective (fun e=>(tail e,head e)))
    (hkinj : Function.Injective (fun e=>(ktail e,khead e)))
    (H₀ Hₖ : V → U → Prop) (J₀ Jₖ : V → V → ℕ) (L₀ Lₖ : V → U → ℕ)
    (hJ0 : ∀ x y,J₀ x y≤occurrenceMultiplicity tail head x y)
    (hJK : ∀ x y,Jₖ x y≤occurrenceMultiplicity ktail khead x y)
    (hL0 : ∀ v u,L₀ v u≤relationMultiplicity H₀ v u)
    (hLK : ∀ v u,Lₖ v u≤relationMultiplicity Hₖ v u)
    (hb : TypedMatrixBalanced q
      (fun x y=>occurrenceMultiplicity tail head x y-J₀ x y)
      (fun x y=>occurrenceMultiplicity ktail khead x y-Jₖ x y)
      (fun v u=>relationMultiplicity H₀ v u-L₀ v u)
      (fun v u=>relationMultiplicity Hₖ v u-Lₖ v u)) :
    TypedMatrixBalanced q
      (occurrenceMultiplicity (fun e : {e // J₀ (tail e) (head e)=0}=>tail e.val) (fun e=>head e.val))
      (occurrenceMultiplicity (fun e : {e // Jₖ (ktail e) (khead e)=0}=>ktail e.val) (fun e=>khead e.val))
      (relationMultiplicity (fun v u=>H₀ v u ∧ L₀ v u=0))
      (relationMultiplicity (fun v u=>Hₖ v u ∧ Lₖ v u=0)) := by
  have h0 := funext fun x=>funext fun y=>occurrenceMultiplicity_matrix_restriction tail head hinj J₀ hJ0 x y
  have hK := funext fun x=>funext fun y=>occurrenceMultiplicity_matrix_restriction ktail khead hkinj Jₖ hJK x y
  have hH0 := funext fun v=>funext fun u=>relationMultiplicity_remainder H₀ L₀ hL0 v u
  have hHK := funext fun v=>funext fun u=>relationMultiplicity_remainder Hₖ Lₖ hLK v u
  rw [h0,hK,hH0,hHK]
  exact hb

end Oberwolfach
