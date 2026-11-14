module

public import Oberwolfach.AlternatingCombinations
public import Oberwolfach.SignedCycleRestriction

@[expose] public section

/-! Restriction to genuine four-cycles and edgewise absolute coefficient loads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem rectangleCombination_fourCycles (H : A → B → Prop)
    (f : A → A → B → B → ℝ)
    (hf : ∀ x y u v,f x y u v≠0 → H x u ∧ H y u ∧ H y v ∧ H x v) (e : A×B) :
    rectangleCombination f e=
      ∑ q : BipartiteFourCycle H,f q.val.1.1 q.val.1.2 q.val.2.1 q.val.2.2*bipartiteFourCycleVector q e := by
  let P (q : (A×A)×(B×B)) := q.1.1≠q.1.2 ∧ q.2.1≠q.2.2 ∧
    H q.1.1 q.2.1 ∧ H q.1.2 q.2.1 ∧ H q.1.2 q.2.2 ∧ H q.1.1 q.2.2
  let g (q : (A×A)×(B×B)) := f q.1.1 q.1.2 q.2.1 q.2.2*
    alternatingRectangle q.1.1 q.1.2 q.2.1 q.2.2 e.1 e.2
  have hz (q : (A×A)×(B×B)) (hq : ¬P q) : g q=0 := by
    rcases q with ⟨⟨x,y⟩,⟨u,v⟩⟩
    dsimp only [g,P] at *
    by_cases hxy : x=y
    · subst y;simp only [alternatingRectangle_repeated_row,mul_zero]
    by_cases huv : u=v
    · subst v;simp only [alternatingRectangle_repeated_column,mul_zero]
    have hf0 : f x y u v=0 := by
      by_contra hn
      exact hq ⟨hxy,huv,hf x y u v hn⟩
    rw [hf0,zero_mul]
  have hh := finite_sum_restrict_of_zero P g hz
  simp only [g,Fintype.sum_prod_type,rectangleCombination,bipartiteFourCycleVector] at hh ⊢
  convert hh using 1
  apply Finset.sum_congr
  · ext q;simp
  · intro q _;rfl

theorem abs_alternatingRectangle_le (x y : A) (u v : B) (a : A) (b : B) :
    |alternatingRectangle x y u v a b|≤
      ((if a=x then (1:ℝ) else 0)+(if a=y then 1 else 0))*
      ((if b=u then (1:ℝ) else 0)+(if b=v then 1 else 0)) := by
  unfold alternatingRectangle
  split_ifs <;> norm_num

theorem full_rectangle_absolute_load (f : A → A → B → B → ℝ)
    (M : ℝ) (hM : 0≤M) (hf : ∀ x y u v,|f x y u v|≤M) (a : A) (b : B) :
    (∑ x,∑ y,∑ u,∑ v,|f x y u v| *|alternatingRectangle x y u v a b|)≤
      4*(Fintype.card A:ℝ)*(Fintype.card B:ℝ)*M := by
  calc
    _ ≤ ∑ x,∑ y,∑ u,∑ v,M*
      (((if a=x then (1:ℝ) else 0)+(if a=y then 1 else 0))*
       ((if b=u then (1:ℝ) else 0)+(if b=v then 1 else 0))) := by
      apply Finset.sum_le_sum;intro x _
      apply Finset.sum_le_sum;intro y _
      apply Finset.sum_le_sum;intro u _
      apply Finset.sum_le_sum;intro v _
      exact mul_le_mul (hf x y u v) (abs_alternatingRectangle_le x y u v a b)
        (abs_nonneg _) hM
    _ = _ := by
      simp only [mul_add,add_mul,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero,
        Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

theorem fourCycle_absolute_load (H : A → B → Prop) (f : A → A → B → B → ℝ)
    (M : ℝ) (hM : 0≤M) (hf : ∀ x y u v,|f x y u v|≤M) (e : A×B) :
    (∑ q : BipartiteFourCycle H,
      |f q.val.1.1 q.val.1.2 q.val.2.1 q.val.2.2| *|bipartiteFourCycleVector q e|)≤
        4*(Fintype.card A:ℝ)*(Fintype.card B:ℝ)*M := by
  let g (q : (A×A)×(B×B)) := |f q.1.1 q.1.2 q.2.1 q.2.2| *
    |alternatingRectangle q.1.1 q.1.2 q.2.1 q.2.2 e.1 e.2|
  have hh := finite_subtype_sum_le
    (fun q : (A×A)×(B×B) => q.1.1≠q.1.2 ∧ q.2.1≠q.2.2 ∧
      H q.1.1 q.2.1 ∧ H q.1.2 q.2.1 ∧ H q.1.2 q.2.2 ∧ H q.1.1 q.2.2)
    g (fun _=>mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hb := full_rectangle_absolute_load f M hM hf e.1 e.2
  have hb' : (∑ i,g i)≤4*(Fintype.card A:ℝ)*(Fintype.card B:ℝ)*M := by
    simpa only [g,Fintype.sum_prod_type] using hb
  have hfinal := hh.trans hb'
  simp only [g,Fintype.sum_prod_type,bipartiteFourCycleVector] at hfinal ⊢
  convert hfinal using 1
  apply Finset.sum_congr
  · ext q;simp
  · intro q _;rfl

end Oberwolfach
