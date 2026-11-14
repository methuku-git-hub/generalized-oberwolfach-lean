module

public import Oberwolfach.WheelLoadCombinations

@[expose] public section

/-! Ordered four-cycles and their alternating edge vectors in an actual
bipartite graph. Repeated rows or columns give the zero vector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def alternatingRectangle {A B : Type*} [DecidableEq A] [DecidableEq B]
    (x y : A) (u v : B) (a : A) (b : B) : ℝ :=
  ((if a=x then (1:ℝ) else 0)-(if a=y then 1 else 0))*
    ((if b=u then (1:ℝ) else 0)-(if b=v then 1 else 0))

abbrev BipartiteFourCycle {A B : Type*} (H : A → B → Prop) :=
  {q : (A×A)×(B×B) // q.1.1≠q.1.2 ∧ q.2.1≠q.2.2 ∧
    H q.1.1 q.2.1 ∧ H q.1.2 q.2.1 ∧ H q.1.2 q.2.2 ∧ H q.1.1 q.2.2}

def bipartiteFourCycleVector {A B : Type*} [DecidableEq A] [DecidableEq B]
    {H : A → B → Prop} (q : BipartiteFourCycle H) (e : A×B) : ℝ :=
  alternatingRectangle q.val.1.1 q.val.1.2 q.val.2.1 q.val.2.2 e.1 e.2

theorem alternatingRectangle_row_sum {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    (x y : A) (u v : B) (a : A) : (∑ b,alternatingRectangle x y u v a b)=0 := by
  unfold alternatingRectangle
  rw [← Finset.mul_sum]
  simp

theorem alternatingRectangle_column_sum {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (x y : A) (u v : B) (b : B) : (∑ a,alternatingRectangle x y u v a b)=0 := by
  unfold alternatingRectangle
  rw [← Finset.sum_mul]
  simp

theorem alternatingRectangle_repeated_row {A B : Type*} [DecidableEq A] [DecidableEq B]
    (x : A) (u v : B) (a : A) (b : B) : alternatingRectangle x x u v a b=0 := by
  simp [alternatingRectangle]

theorem alternatingRectangle_repeated_column {A B : Type*} [DecidableEq A] [DecidableEq B]
    (x y : A) (u : B) (a : A) (b : B) : alternatingRectangle x y u u a b=0 := by
  simp [alternatingRectangle]

theorem bipartiteFourCycleVector_outside {A B : Type*} [DecidableEq A] [DecidableEq B]
    {H : A → B → Prop} (q : BipartiteFourCycle H) (e : A×B) (he : ¬H e.1 e.2) :
    bipartiteFourCycleVector q e=0 := by
  rcases q with ⟨⟨⟨x,y⟩,⟨u,v⟩⟩,hxy,huv,hxu,hyu,hyv,hxv⟩
  rcases e with ⟨a,b⟩
  dsimp only [bipartiteFourCycleVector,alternatingRectangle]
  split_ifs <;> simp_all

def zeroMarginalSpace {A B : Type*} [Fintype A] [Fintype B]
    (H : A → B → Prop) : Submodule ℝ (A×B → ℝ) where
  carrier := {z | (∀ a b,¬H a b → z (a,b)=0) ∧
    (∀ a,∑ b,z (a,b)=0) ∧ (∀ b,∑ a,z (a,b)=0)}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw
    refine ⟨?_,?_,?_⟩
    · intro a b hab;simp only [Pi.add_apply,hz.1 a b hab,hw.1 a b hab,add_zero]
    · intro a;simp only [Pi.add_apply,Finset.sum_add_distrib,hz.2.1 a,hw.2.1 a,add_zero]
    · intro b;simp only [Pi.add_apply,Finset.sum_add_distrib,hz.2.2 b,hw.2.2 b,add_zero]
  smul_mem' := by
    intro c z hz
    refine ⟨?_,?_,?_⟩
    · intro a b hab;simp only [Pi.smul_apply,smul_eq_mul,hz.1 a b hab,mul_zero]
    · intro a;simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hz.2.1 a,mul_zero]
    · intro b;simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hz.2.2 b,mul_zero]

theorem bipartiteFourCycleVector_zero_marginals {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {H : A → B → Prop} (q : BipartiteFourCycle H) :
    bipartiteFourCycleVector q∈zeroMarginalSpace H := by
  refine ⟨fun a b hab => bipartiteFourCycleVector_outside q (a,b) hab,?_,?_⟩
  · intro a
    exact alternatingRectangle_row_sum _ _ _ _ _
  · intro b
    exact alternatingRectangle_column_sum _ _ _ _ _

end Oberwolfach
