module

public import Oberwolfach.LongPathReserve

@[expose] public section

/-! Normalizing locally balanced capacities gives the transition system and
stationary degree profiles used by the long-interval theorem. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def capacityTransition {X : Type*}
    (a : ℕ → X → X → ℝ) (d : ℕ → X → ℝ) (i : ℕ) (x y : X) : ℝ := a i x y/d i x

def capacityProfile {X : Type*} (d : ℕ → X → ℝ) (M : ℝ) (i : ℕ) (x : X) : ℝ := d i x/M

theorem capacityTransition_isTransition {X : Type*} [Fintype X]
    (a : ℕ → X → X → ℝ) (d : ℕ → X → ℝ)
    (ha : ∀ i x y, 0 ≤ a i x y) (hd : ∀ i x, 0 < d i x)
    (hrow : ∀ i x, ∑ y, a i x y=d i x) :
    ∀ i, IsTransition (capacityTransition a d i) := by
  intro i
  constructor
  · intro x y
    exact div_nonneg (ha i x y) (hd i x).le
  · intro x
    change (∑ y, a i x y/d i x)=1
    rw [← Finset.sum_div,hrow,div_self (hd i x).ne']

theorem capacityProfile_stationary {X : Type*} [Fintype X]
    (a : ℕ → X → X → ℝ) (d : ℕ → X → ℝ) (M : ℝ)
    (hd : ∀ i x, 0 < d i x) (hcol : ∀ i y, ∑ x, a i x y=d (i+1) y) :
    ∀ i, transitionApply (capacityProfile d M i) (capacityTransition a d i)=capacityProfile d M (i+1) := by
  intro i
  funext y
  change (∑ x, (d i x/M)*(a i x y/d i x))=d (i+1) y/M
  have heq (x : X) : (d i x/M)*(a i x y/d i x)=a i x y/M := by
    field_simp [(hd i x).ne']
  simp_rw [heq]
  rw [← Finset.sum_div,hcol]

theorem capacityProfile_distribution {X : Type*} [Fintype X]
    (d : ℕ → X → ℝ) (M : ℝ) (hM : 0 < M)
    (hd : ∀ i x, 0 < d i x) (hs : ∀ i, ∑ x, d i x=M) :
    (∀ i x, 0 < capacityProfile d M i x) ∧ (∀ i, ∑ x, capacityProfile d M i x=1) := by
  constructor
  · intro i x
    exact div_pos (hd i x) hM
  · intro i
    change (∑ x, d i x/M)=1
    rw [← Finset.sum_div,hs,div_self hM.ne']

theorem capacityTransition_reconstruct {X : Type*}
    (a : ℕ → X → X → ℝ) (d : ℕ → X → ℝ) (M : ℝ) (hM : M ≠ 0)
    (hd : ∀ i x, d i x ≠ 0) (i : ℕ) (x y : X) :
    M*capacityProfile d M i x*capacityTransition a d i x y=a i x y := by
  unfold capacityProfile capacityTransition
  field_simp [hM,hd i x]

theorem reservedPathWeight_continuous {T X : Type*} [TopologicalSpace T] [Fintype X]
    (R : ℕ → X → X → ℝ) (i k : ℕ) (Q : T → X → X → ℝ)
    (hQ : ∀ x z, Continuous (fun t => Q t x z)) :
    ∀ p : Fin (k+1) → X, Continuous (fun t => reservedPathWeight R i k (Q t) p) := by
  intro p
  exact ((hQ _ _).mul_const _).div_const _

end Oberwolfach
