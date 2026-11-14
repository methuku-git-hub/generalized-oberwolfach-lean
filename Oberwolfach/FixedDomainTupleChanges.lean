module

public import Oberwolfach.TupleRelationDeletionCounts

@[expose] public section

/-! Tuple-family loss at the original inner-domain scale. Fixed roots,
physical-edge tests and separation predicates remain inside P and Q;
each lost tuple is charged to a changed free coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

def fixedDomainTuplePredicateEquiv (A : Finset V) (P : (I→V)→Prop)
    (hP : ∀ f,P f → ∀ i,f i∈A) :
    {f : I→V // P f} ≃ {f : I→A // P (fun i=>(f i).val)} where
  toFun f := ⟨fun i=>⟨f.val i,hP f.val f.property i⟩,f.property⟩
  invFun f := ⟨fun i=>(f.val i).val,f.property⟩
  left_inv f := by apply Subtype.ext;rfl
  right_inv f := by apply Subtype.ext;funext i;apply Subtype.ext;rfl

theorem fixedDomainTuple_predicate_loss (A : Finset V) (P Q : (I→V)→Prop)
    (hP : ∀ f,P f → ∀ i,f i∈A) (hQ : ∀ f,Q f → ∀ i,f i∈A)
    (D : I→Finset V) (δ : ℝ) (hD : ∀ i,((D i).card:ℝ)≤δ)
    (hbad : ∀ f,P f → ¬Q f → ∃ i,f i∈D i) :
    (Fintype.card {f : I→V // P f}:ℝ)-Fintype.card {f : I→V // Q f}≤
      Fintype.card I*δ*(A.card:ℝ)^(Fintype.card I-1) := by
  rw [Fintype.card_congr (fixedDomainTuplePredicateEquiv A P hP),
    Fintype.card_congr (fixedDomainTuplePredicateEquiv A Q hQ)]
  have hh := finite_predicate_loss_union
    (fun f : I→A=>P (fun i=>(f i).val)) (fun f : I→A=>Q (fun i=>(f i).val))
    (fun i (f : I→A)=>(f i).val∈D i) (by intro f hp hq;exact hbad _ hp hq)
  apply hh.trans
  calc
    _ ≤ ∑ _i : I,δ*(Fintype.card A:ℝ)^(Fintype.card I-1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply tuple_unary_deletion_count (fun x : A=>x.val∈D i) i δ
      calc
        _ ≤ ∑ x : V,if x∈D i then (1:ℝ) else 0 := by
          have hs := finite_injective_sum_le (Subtype.val : A→V) Subtype.val_injective
            (fun x=>if x∈D i then (1:ℝ) else 0) (fun _=>by split_ifs <;> norm_num)
          convert hs using 1 <;> apply Finset.sum_congr rfl <;> intro x hx <;> split_ifs <;> rfl
        _ = ((D i).card:ℝ) := by
          rw [← Finset.sum_filter]
          simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,mul_one]
        _ ≤ δ := hD i
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe];ring

end Oberwolfach
