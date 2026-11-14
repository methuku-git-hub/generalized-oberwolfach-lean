module

public import Oberwolfach.DirectedEdgeIndicators
public import Oberwolfach.TwistedTupleEdges
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! Canonical marked cycles start immediately after their unique marked arc.
Their edge incidence vectors lie in the exact balance subspace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def IsMarkedCycleTuple {V E K : Type*} (tail head : E → V) (ktail khead : K → V)
    (m : ℕ) (π : Equiv.Perm V) (b : ℕ) (C : Fin (m+1) → V) : Prop :=
  PermutationSeparated π b C ∧
  (∀ j : Fin m,∃ e,tail e=C j.castSucc ∧ head e=C j.succ) ∧
  ∃ e,ktail e=C (Fin.last m) ∧ khead e=C 0

abbrev MarkedCycleTuple {V E K : Type*} (tail head : E → V) (ktail khead : K → V)
    (m : ℕ) (π : Equiv.Perm V) (b : ℕ) :=
  {C : Fin (m+1) → V // IsMarkedCycleTuple tail head ktail khead m π b C}

def markedCycleIncidence {V E K : Type*} [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (C : Fin (m+1) → V) : E⊕K → ℝ :=
  Sum.elim (fun e => ∑ j : Fin m,directedEdgeIndicator tail head (C j.castSucc) (C j.succ) e)
    (directedEdgeIndicator ktail khead (C (Fin.last m)) (C 0))

def markedBalanceSubspace {V E K : Type*} [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) : Submodule ℝ (E⊕K → ℝ) where
  carrier := {w | occurrenceSumLinear (Sum.elim tail ktail) w=occurrenceSumLinear (Sum.elim head khead) w ∧
    (∑ e : E,w (Sum.inl e))=(m:ℝ)*(∑ e : K,w (Sum.inr e))}
  zero_mem' := by simp
  add_mem' := by
    intro w u hw hu
    constructor
    · simp only [map_add,hw.1,hu.1]
    · simp only [Pi.add_apply,Finset.sum_add_distrib,hw.2,hu.2,mul_add]
  smul_mem' := by
    intro a w hw
    constructor
    · simp only [map_smul,hw.1]
    · simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hw.2]
      ring

theorem markedCycleIncidence_nonneg {V E K : Type*} [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (C : Fin (m+1) → V) (e : E⊕K) :
    0≤markedCycleIncidence tail head ktail khead m C e := by
  cases e with
  | inl e =>
    simp only [markedCycleIncidence,Sum.elim_inl]
    apply Finset.sum_nonneg
    intro j _
    unfold directedEdgeIndicator
    split_ifs <;> norm_num
  | inr e =>
    simp only [markedCycleIncidence,Sum.elim_inr,directedEdgeIndicator]
    split_ifs <;> norm_num

theorem markedCycleIncidence_balanced {V E K : Type*} [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V)
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (m : ℕ) (C : Fin (m+1) → V)
    (hO : ∀ j : Fin m,∃ e,tail e=C j.castSucc ∧ head e=C j.succ)
    (hK : ∃ e,ktail e=C (Fin.last m) ∧ khead e=C 0) :
    markedCycleIncidence tail head ktail khead m C∈markedBalanceSubspace tail head ktail khead m := by
  classical
  constructor
  · funext v
    change (∑ e : E⊕K,if Sum.elim tail ktail e=v then markedCycleIncidence tail head ktail khead m C e else 0)=
      ∑ e : E⊕K,if Sum.elim head khead e=v then markedCycleIncidence tail head ktail khead m C e else 0
    simp only [Fintype.sum_sum_type,markedCycleIncidence,Sum.elim_inl,Sum.elim_inr]
    have ho (f : E → V) : (∑ e,if f e=v then (∑ j : Fin m,directedEdgeIndicator tail head (C j.castSucc) (C j.succ) e) else 0)=
        ∑ j : Fin m,occurrenceSumLinear f (directedEdgeIndicator tail head (C j.castSucc) (C j.succ)) v := by
      calc
        _ = ∑ e,∑ j : Fin m,if f e=v then directedEdgeIndicator tail head (C j.castSucc) (C j.succ) e else 0 := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases h : f e=v <;> simp only [h,ite_true,ite_false,Finset.sum_const_zero]
        _ = _ := Finset.sum_comm
    rw [ho tail,ho head]
    change (∑ j : Fin m,occurrenceSumLinear tail (directedEdgeIndicator tail head (C j.castSucc) (C j.succ)) v)+
      occurrenceSumLinear ktail (directedEdgeIndicator ktail khead (C (Fin.last m)) (C 0)) v=
      (∑ j : Fin m,occurrenceSumLinear head (directedEdgeIndicator tail head (C j.castSucc) (C j.succ)) v)+
      occurrenceSumLinear khead (directedEdgeIndicator ktail khead (C (Fin.last m)) (C 0)) v
    simp only [directedEdgeIndicator_tail tail head hinj _ _ (hO _),
      directedEdgeIndicator_head tail head hinj _ _ (hO _),
      directedEdgeIndicator_tail ktail khead hkinj _ _ hK,
      directedEdgeIndicator_head ktail khead hkinj _ _ hK]
    have hfirst := Fin.sum_univ_castSucc (fun j : Fin (m+1) => if C j=v then (1:ℝ) else 0)
    have hlast := Fin.sum_univ_succ (fun j : Fin (m+1) => if C j=v then (1:ℝ) else 0)
    linarith
  · change (∑ e : E,∑ j : Fin m,directedEdgeIndicator tail head (C j.castSucc) (C j.succ) e)=
      (m:ℝ)*(∑ e : K,directedEdgeIndicator ktail khead (C (Fin.last m)) (C 0) e)
    rw [Finset.sum_comm]
    simp only [directedEdgeIndicator_total tail head hinj _ _ (hO _),
      directedEdgeIndicator_total ktail khead hkinj _ _ hK,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

end Oberwolfach
