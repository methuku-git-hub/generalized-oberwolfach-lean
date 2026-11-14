module

public import Oberwolfach.OccurrenceCapacityMatrix
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-! The copied graph has one ordinary interface at each of the first m
positions and one marked interface at the last position. Edge occurrences
retain their types; balance is checked at every copied vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def copiedMarkedCapacity {V E K : Type*} [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ)
    (f : Fin m → E → ℝ) (wK : K → ℝ) : Fin (m+1) → V → V → ℝ :=
  Fin.snoc (fun j => occurrenceCapacityMatrix tail head (f j))
    (occurrenceCapacityMatrix ktail khead wK)

@[simp] theorem copiedMarkedCapacity_ordinary {V E K : Type*} [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ)
    (f : Fin m → E → ℝ) (wK : K → ℝ) (j : Fin m) (x y : V) :
    copiedMarkedCapacity tail head ktail khead m f wK j.castSucc x y=
      occurrenceCapacityMatrix tail head (f j) x y := by
  exact congrFun (congrFun (Fin.snoc_castSucc _ _ j) x) y

@[simp] theorem copiedMarkedCapacity_marked {V E K : Type*} [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ)
    (f : Fin m → E → ℝ) (wK : K → ℝ) (x y : V) :
    copiedMarkedCapacity tail head ktail khead m f wK (Fin.last m) x y=
      occurrenceCapacityMatrix ktail khead wK x y := by
  exact congrFun (congrFun (Fin.snoc_last _ _) x) y

theorem finRotate_castSucc_eq_succ (m : ℕ) (j : Fin m) :
    finRotate (m+1) j.castSucc=j.succ := by
  exact finRotate_of_lt j.isLt

theorem copiedMarkedCapacity_balance {V E K : Type*} [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ)
    (f : Fin m → E → ℝ) (wK : K → ℝ) (d : Fin (m+1) → V → ℝ)
    (hfr : ∀ j v,occurrenceSumLinear tail (f j) v=d j.castSucc v)
    (hfc : ∀ j v,occurrenceSumLinear head (f j) v=d j.succ v)
    (hkr : ∀ v,occurrenceSumLinear ktail wK v=d (Fin.last m) v)
    (hkc : ∀ v,occurrenceSumLinear khead wK v=d 0 v) :
    (∀ i x,(∑ y,copiedMarkedCapacity tail head ktail khead m f wK i x y)=d i x) ∧
    (∀ i y,(∑ x,copiedMarkedCapacity tail head ktail khead m f wK i x y)=d (finRotate (m+1) i) y) := by
  constructor
  · intro i x
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [copiedMarkedCapacity_marked,occurrenceCapacityMatrix_row,hkr]
    · simp only [copiedMarkedCapacity_ordinary,occurrenceCapacityMatrix_row,hfr]
  · intro i y
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [copiedMarkedCapacity_marked,occurrenceCapacityMatrix_col,finRotate_last,hkc]
    · simp only [copiedMarkedCapacity_ordinary,occurrenceCapacityMatrix_col,finRotate_castSucc_eq_succ,hfc]

theorem occurrenceCapacityMatrix_pos_iff {V E : Type*} [Fintype E] [DecidableEq V]
    (tail head : E → V) (hinj : Function.Injective (fun e => (tail e,head e)))
    (w : E → ℝ) (hw : ∀ e,0<w e) (x y : V) :
    0<occurrenceCapacityMatrix tail head w x y ↔ ∃ e,tail e=x ∧ head e=y := by
  constructor
  · intro h
    by_contra hn
    rw [occurrenceCapacityMatrix_zero tail head w x y hn] at h
    exact (lt_irrefl _ h)
  · rintro ⟨e,rfl,rfl⟩
    rw [occurrenceCapacityMatrix_at_edge tail head hinj w]
    exact hw e

theorem copiedMarkedCapacity_bounds {V E K : Type*} [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V)
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (m : ℕ) (hm : 1≤m) (f : Fin m → E → ℝ) (wK : K → ℝ)
    (hf : ∀ j e,1/(2*(m:ℝ))≤f j e ∧ f j e≤2/(m:ℝ))
    (hwK : ∀ e,1/2≤wK e ∧ wK e≤3/2) :
    (∀ i x y,0≤copiedMarkedCapacity tail head ktail khead m f wK i x y) ∧
    (∀ i x y,0<copiedMarkedCapacity tail head ktail khead m f wK i x y →
      1/(2*(m:ℝ))≤copiedMarkedCapacity tail head ktail khead m f wK i x y ∧
      copiedMarkedCapacity tail head ktail khead m f wK i x y≤2) := by
  have hmr : (1:ℝ)≤m := by exact_mod_cast hm
  have hmpos : (0:ℝ)<m := by linarith
  constructor
  · intro i x y
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [copiedMarkedCapacity_marked]
      exact occurrenceCapacityMatrix_nonneg ktail khead wK (fun e => by linarith [(hwK e).1]) x y
    · simp only [copiedMarkedCapacity_ordinary]
      exact occurrenceCapacityMatrix_nonneg tail head (f _) (fun e =>
        (by positivity : (0:ℝ)≤1/(2*m)).trans (hf _ e).1) x y
  · intro i x y
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [copiedMarkedCapacity_marked]
      intro hpos
      obtain ⟨hl,hu⟩ := occurrenceCapacityMatrix_positive_bounds ktail khead hkinj wK (1/2) (3/2) hwK x y hpos
      constructor
      · apply le_trans _ hl
        apply (div_le_iff₀ (by positivity)).mpr
        linarith
      · linarith
    · simp only [copiedMarkedCapacity_ordinary]
      intro hpos
      obtain ⟨hl,hu⟩ := occurrenceCapacityMatrix_positive_bounds tail head hinj (f j) (1/(2*m)) (2/m) (hf j) x y hpos
      refine ⟨hl,hu.trans ?_⟩
      apply (div_le_iff₀ hmpos).mpr
      linarith

end Oberwolfach
