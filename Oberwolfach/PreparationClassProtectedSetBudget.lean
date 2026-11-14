module

public import Oberwolfach.ProtectedSets

@[expose] public section
/-! A long class and at most K+1 retained classes share one protected-set
budget. The long class occurs at most once because class labels are distinct. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem preparation_class_protected_set_budget {n k K:ℕ}
    (label:Fin k↪Option (Fin K)) (I:Fin k→Finset (Fin n)) (εL εS:ℝ)
    (hL:0≤εL) (hS:0≤εS) (hk:k≤K+1)
    (hI:∀a,((I a).card:ℝ)≤(if label a=none then εL else εS)*n):
    ((∑a,(I a).card:ℕ):ℝ)≤(εL+(K+1)*εS)*n :=by
  have hsingle:(∑a:Fin k,if label a=none then εL else 0)≤εL:=by
    by_cases hex:∃a:Fin k,label a=none
    · obtain ⟨a,ha⟩:=hex
      have heq:∀b:Fin k,label b=none↔b=a:=by
        intro b
        constructor
        · intro hb
          exact label.injective (hb.trans ha.symm)
        · intro hb
          simpa [hb] using ha
      simp only [heq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      exact le_rfl
    · simp only [not_exists] at hex
      simp [hex,hL]
  have hbudget:(∑a:Fin k,if label a=none then εL else εS)≤εL+(K+1)*εS:=by
    have hs:(∑a:Fin k,if label a=none then εL else εS)≤
        ∑a:Fin k,((if label a=none then εL else 0)+εS):=by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs <;> linarith
    have hkR:(k:ℝ)≤K+1:=by exact_mod_cast hk
    have hm:(k:ℝ)*εS≤(K+1)*εS:=mul_le_mul_of_nonneg_right hkR hS
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    linarith
  have hsums:((∑a,(I a).card:ℕ):ℝ)≤∑a:Fin k,(if label a=none then εL else εS)*n:=by
    push_cast
    exact Finset.sum_le_sum (fun a _=>hI a)
  rw [←Finset.sum_mul] at hsums
  exact hsums.trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg n))
end Oberwolfach
