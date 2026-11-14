module

public import Oberwolfach.RootedEdgeChanges
public import Oberwolfach.OrdinaryCycleCountBounds

@[expose] public section

/-! Weighted rooted pattern sums with fixed candidates, root values,
coefficient functions, and masks. Both insertions and deletions are allowed;
no presence of a root edge is assumed or conditioned on. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem conjunction_indicator_change {J : Type*} [Fintype J]
    (P Q D : J → Prop) (h : ∀ j,¬D j → (P j ↔ Q j)) :
    |(if ∀ j,Q j then (1:ℝ) else 0)-(if ∀ j,P j then 1 else 0)|≤
      ∑ j,if D j then (1:ℝ) else 0 := by
  classical
  by_cases he : ∃ j,D j
  · obtain ⟨j,hj⟩ := he
    have hsum := Finset.single_le_sum (s:=Finset.univ) (f:=fun j=>if D j then (1:ℝ) else 0)
      (fun _ _=>by split_ifs <;> norm_num) (Finset.mem_univ j)
    rw [if_pos hj] at hsum
    have hdiff : |(if ∀ j,Q j then (1:ℝ) else 0)-(if ∀ j,P j then 1 else 0)|≤1 := by
      split_ifs <;> norm_num
    exact hdiff.trans hsum
  · have heq : (∀ j,P j) ↔ (∀ j,Q j) := forall_congr' (fun j=>h j (fun hd=>he ⟨j,hd⟩))
    simp only [heq,sub_self,abs_zero]
    exact Finset.sum_nonneg (fun _ _=>by split_ifs <;> norm_num)

def rootedPatternValue {I J X : Type*} [Fintype J]
    (active : J → (I → X) → Prop) (a b : J → X⊕I)
    (σ τ : J → Equiv.Perm X) (G : J → X → X → Prop) (f : I → X) : ℝ :=
  if ∀ j,active j f → G j (σ j (rootedPositionValue f (a j))) (τ j (rootedPositionValue f (b j)))
    then 1 else 0

theorem rootedPatternValue_change {I J X : Type*} [Fintype J]
    (active : J → (I → X) → Prop) (a b : J → X⊕I)
    (σ τ : J → Equiv.Perm X) (G G' D : J → X → X → Prop)
    (hchange : ∀ j x y,¬D j x y → (G j x y ↔ G' j x y)) (f : I → X) :
    |rootedPatternValue active a b σ τ G' f-rootedPatternValue active a b σ τ G f|≤
      ∑ j,if D j (σ j (rootedPositionValue f (a j))) (τ j (rootedPositionValue f (b j))) then (1:ℝ) else 0 := by
  have hh := conjunction_indicator_change
    (fun j=>active j f → G j (σ j (rootedPositionValue f (a j))) (τ j (rootedPositionValue f (b j))))
    (fun j=>active j f → G' j (σ j (rootedPositionValue f (a j))) (τ j (rootedPositionValue f (b j))))
    (fun j=>D j (σ j (rootedPositionValue f (a j))) (τ j (rootedPositionValue f (b j))))
    (by
      intro j hj
      constructor
      · intro hq ha;exact (hchange j _ _ hj).mp (hq ha)
      · intro hq ha;exact (hchange j _ _ hj).mpr (hq ha))
  convert hh using 1 <;> unfold rootedPatternValue <;> split_ifs <;> rfl

theorem weighted_rooted_pattern_stability {I J X C : Type*}
    [Fintype I] [Fintype J] [Fintype X] [Fintype C] [DecidableEq I]
    (encode : C → (I → X)) (hinj : Function.Injective encode)
    (active : J → (I → X) → Prop) (a b : J → X⊕I)
    (hab : ∀ j,RootedEdgeHasFreeEndpoint (a j) (b j))
    (σ τ : J → Equiv.Perm X) (G G' D : J → X → X → Prop)
    (hchange : ∀ j x y,¬D j x y → (G j x y ↔ G' j x y))
    (d M : ℝ) (hM : 0≤M)
    (hout : ∀ j x,(∑ y,if D j x y then (1:ℝ) else 0)≤d)
    (hin : ∀ j y,(∑ x,if D j x y then (1:ℝ) else 0)≤d)
    (w : C → ℝ) (hw : ∀ c,0≤w c ∧ w c≤M) :
    |(∑ c,w c*rootedPatternValue active a b σ τ G' (encode c))-
      (∑ c,w c*rootedPatternValue active a b σ τ G (encode c))|≤
      M*Fintype.card J*(Fintype.card X:ℝ)^(Fintype.card I-1)*d := by
  classical
  let count (f : I → X) : ℝ :=
    ∑ j,if D j (σ j (rootedPositionValue f (a j))) (τ j (rootedPositionValue f (b j))) then 1 else 0
  have hcount (f : I → X) : 0≤count f := Finset.sum_nonneg (fun _ _=>by split_ifs <;> norm_num)
  have hdiff (c : C) :
      |w c*rootedPatternValue active a b σ τ G' (encode c)-w c*rootedPatternValue active a b σ τ G (encode c)|≤
      M*count (encode c) := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (hw c).1]
    exact (mul_le_mul_of_nonneg_left (rootedPatternValue_change active a b σ τ G G' D hchange (encode c))
      (hw c).1).trans (mul_le_mul_of_nonneg_right (hw c).2 (hcount _))
  have htotal : (∑ f : I → X,count f)≤
      (Fintype.card J:ℝ)*(Fintype.card X:ℝ)^(Fintype.card I-1)*d := by
    unfold count
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _j : J,(Fintype.card X:ℝ)^(Fintype.card I-1)*d :=
        Finset.sum_le_sum (fun j _=>rooted_edge_change_count (D j) d (hout j) (hin j) (a j) (b j) (hab j) (σ j) (τ j))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
  calc
    _ ≤ ∑ c,|w c*rootedPatternValue active a b σ τ G' (encode c)-w c*rootedPatternValue active a b σ τ G (encode c)| := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c,M*count (encode c) := Finset.sum_le_sum (fun c _=>hdiff c)
    _ = M*∑ c,count (encode c) := (Finset.mul_sum _ _ _).symm
    _ ≤ M*∑ f : I → X,count f := mul_le_mul_of_nonneg_left (finite_injective_sum_le encode hinj count hcount) hM
    _ ≤ M*((Fintype.card J:ℝ)*(Fintype.card X:ℝ)^(Fintype.card I-1)*d) := mul_le_mul_of_nonneg_left htotal hM
    _ = _ := by ring

end Oberwolfach
