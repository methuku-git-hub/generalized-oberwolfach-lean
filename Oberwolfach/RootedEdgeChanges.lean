module

public import Oberwolfach.FixedCoordinateCounts
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

/-! Counts of tuples affected by a changed edge. At least one endpoint is
free. The degree of the realised change relation, not a sampling density,
controls the number of assignments. The endpoint permutations are fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I]

def fillFreeCoordinate (i : I) (x : X) (g : {j : I // j≠i} → X) : I → X :=
  fun j=>if h : j=i then x else g ⟨j,h⟩

theorem sum_bound_from_one_coordinate (i : I) (F : (I → X) → ℝ) (d : ℝ)
    (h : ∀ g : {j : I // j≠i} → X,∑ x,F (fillFreeCoordinate i x g)≤d) :
    (∑ f : I → X,F f)≤(Fintype.card X:ℝ)^(Fintype.card I-1)*d := by
  classical
  have he : (∑ f : I → X,F f)=
      ∑ g : {j : I // j≠i} → X,∑ x,F (fillFreeCoordinate i x g) := by
    rw [← (Equiv.funSplitAt i X).symm.sum_comp F,Fintype.sum_prod_type,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    funext j
    by_cases hj : j=i
    · subst j;simp [Equiv.funSplitAt,Equiv.piSplitAt,fillFreeCoordinate]
    · simp [Equiv.funSplitAt,Equiv.piSplitAt,fillFreeCoordinate,hj]
  rw [he]
  calc
    _ ≤ ∑ _g : {j : I // j≠i} → X,d := Finset.sum_le_sum (fun g _=>h g)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fun,
        Fintype.card_subtype_compl,Fintype.card_unique,Nat.cast_pow]

def rootedPositionValue (f : I → X) : X⊕I → X := Sum.elim id f

def RootedEdgeHasFreeEndpoint (a b : X⊕I) : Prop :=
  match a,b with
  | Sum.inl _,Sum.inl _ => False
  | Sum.inr i,Sum.inr j => i≠j
  | _,_ => True

theorem rooted_edge_change_count
    (D : X → X → Prop) (d : ℝ)
    (hout : ∀ x,(∑ y,if D x y then (1:ℝ) else 0)≤d)
    (hin : ∀ y,(∑ x,if D x y then (1:ℝ) else 0)≤d)
    (a b : X⊕I) (hab : RootedEdgeHasFreeEndpoint a b)
    (σ τ : Equiv.Perm X) :
    (∑ f : I → X,if D (σ (rootedPositionValue f a)) (τ (rootedPositionValue f b)) then (1:ℝ) else 0)≤
      (Fintype.card X:ℝ)^(Fintype.card I-1)*d := by
  classical
  cases a with
  | inl x =>
    cases b with
    | inl y => exact hab.elim
    | inr j =>
      apply sum_bound_from_one_coordinate j
      intro g
      simp only [rootedPositionValue,Sum.elim_inl,Sum.elim_inr,id_eq,fillFreeCoordinate,dif_pos rfl,dite_true]
      rw [Equiv.sum_comp τ (fun y=>if D (σ x) y then (1:ℝ) else 0)]
      exact hout (σ x)
  | inr i =>
    cases b with
    | inl y =>
      apply sum_bound_from_one_coordinate i
      intro g
      simp only [rootedPositionValue,Sum.elim_inl,Sum.elim_inr,id_eq,fillFreeCoordinate,dif_pos rfl,dite_true]
      rw [Equiv.sum_comp σ (fun x=>if D x (τ y) then (1:ℝ) else 0)]
      exact hin (τ y)
    | inr j =>
      have hne : i≠j := hab
      apply sum_bound_from_one_coordinate j
      intro g
      simp only [rootedPositionValue,Sum.elim_inr,fillFreeCoordinate,dif_pos rfl,dif_neg hne,dite_true]
      rw [Equiv.sum_comp τ (fun y=>if D (σ (g ⟨i,hne⟩)) y then (1:ℝ) else 0)]
      exact hout (σ (g ⟨i,hne⟩))

end Oberwolfach
