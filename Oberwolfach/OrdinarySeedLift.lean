module

public import Oberwolfach.OrdinaryWheelLoads
public import Oberwolfach.OrdinaryCycleWeightRestriction

@[expose] public section

/-! Exact reindexing of the full-hub wheel family. Each physical admissible
cycle occurs once for every hub; the fixed cycle weights are not resampled. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable

variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (P F : SimpleGraph V) (r : ℕ)

def ordinaryFullHubWheelEquiv :
    OrdinaryWheel P F (fun _ : V=>fun _ : U=>True) r ≃
      ({C : OrdinaryCycle P r // ∀ v∈C.val.val.support,∀ z∈C.val.val.support,¬F.Adj v z}×U) where
  toFun W:=(⟨W.val.1,W.property.2⟩,W.val.2)
  invFun a:=⟨(a.1.val,a.2),⟨fun _ _=>True.intro,a.1.property⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

def ordinaryCycleWheelWeight (weight : OrdinaryCycle P r → ℝ) (denom : ℝ)
    (W : OrdinaryWheel P F (fun _ : V=>fun _ : U=>True) r) : ℝ := weight W.val.1/denom

theorem ordinaryFullHubWheel_sum (f : OrdinaryCycle P r → U → ℝ) :
    (∑ W : OrdinaryWheel P F (fun _ : V=>fun _ : U=>True) r,f W.val.1 W.val.2)=
      ∑ C,if (∀ v∈C.val.val.support,∀ z∈C.val.val.support,¬F.Adj v z) then ∑ u,f C u else 0 := by
  let good := fun C : OrdinaryCycle P r=>∀ v∈C.val.val.support,∀ z∈C.val.val.support,¬F.Adj v z
  have hh := finite_sum_restrict_of_zero good (fun C=>if good C then ∑ u,f C u else 0)
    (fun C h=>if_neg h)
  have hsum := (ordinaryFullHubWheelEquiv (U:=U) P F r).symm.sum_comp
    (fun W : OrdinaryWheel P F (fun _ : V=>fun _ : U=>True) r=>f W.val.1 W.val.2)
  dsimp only [ordinaryFullHubWheelEquiv,Equiv.coe_fn_symm_mk] at hsum
  rw [Fintype.sum_prod_type] at hsum
  calc
    _ = ∑ C : {C : OrdinaryCycle P r // good C},∑ u,f C.val u := hsum.symm
    _ = ∑ C : {C : OrdinaryCycle P r // good C},if good C.val then ∑ u,f C.val u else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      exact (if_pos C.property).symm
    _ = _ := hh.symm


set_option maxHeartbeats 100000 in
theorem ordinaryCycleWheelWeight_rim_load (weight : OrdinaryCycle P r → ℝ) (denom : ℝ) (x y : V) :
    ordinaryRimLoad (ordinaryCycleWheelWeight (U:=U) P F r weight denom) x y=
      (Fintype.card U:ℝ)/denom *
        ∑ C : OrdinaryCycle P r,if C.val.val.Adj x y ∧ (∀ v∈C.val.val.support,∀ z∈C.val.val.support,¬F.Adj v z)
          then weight C else 0 := by
  unfold ordinaryRimLoad ordinaryCycleWheelWeight ordinaryWheelRim
  have hh := ordinaryFullHubWheel_sum P F r
    (fun C (_ : U)=>if C.val.val.Adj x y then weight C/denom else 0)
  calc
    _ = ∑ C : OrdinaryCycle P r,if (∀ v∈C.val.val.support,∀ z∈C.val.val.support,¬F.Adj v z) then
        ∑ _u : U,if C.val.val.Adj x y then weight C/denom else 0 else 0 := by
      convert hh using 1 <;> congr!
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C _
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      by_cases he : C.val.val.Adj x y
      · simp only [he,ite_true,true_and]
        split_ifs <;> ring
      · simp only [he,ite_false,false_and,ite_self,mul_zero]




theorem ordinaryCycleWheelWeight_spoke_load (weight : OrdinaryCycle P r → ℝ) (denom : ℝ) (v : V) (u : U) :
    ordinarySpokeLoad (ordinaryCycleWheelWeight P F r weight denom) v u=
      1/denom *
        ∑ C,if v∈C.val.val.support ∧ (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y)
          then weight C else 0 := by
  unfold ordinarySpokeLoad ordinaryCycleWheelWeight ordinaryWheelRim ordinaryWheelHub
  have hh := ordinaryFullHubWheel_sum P F r (fun C a=>if a=u ∧ v∈C.val.val.support then weight C/denom else 0)
  calc
    _ = ∑ C,if (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y) then
        ∑ a : U,if a=u ∧ v∈C.val.val.support then weight C/denom else 0 else 0 := by
      convert hh using 1 <;> congr!
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C _
      by_cases hv : v∈C.val.val.support
      · simp only [hv,and_true,true_and]
        simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
        split_ifs <;> ring
      · simp only [hv,and_false,false_and,ite_false,Finset.sum_const_zero,ite_self,mul_zero]

end Oberwolfach
