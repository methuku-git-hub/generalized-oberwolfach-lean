module

public import Mathlib.Analysis.Convex.Birkhoff
public import Oberwolfach.FiniteSampling

@[expose] public section

/-! A finite law on bijections with prescribed bistochastic edge marginals.
Birkhoff's theorem is imported as its proved mathlib theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bistochastic_sampling {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (M : X → Y → ℝ) (hM : ∀ x y, 0 ≤ M x y)
    (hrow : ∀ x, ∑ y, M x y = 1) (hcol : ∀ y, ∑ x, M x y = 1) :
    ∃ μ : FiniteLaw (Equiv.Perm X),
      ∀ x y, (∑ σ, if e (σ x) = y then μ.mass σ else 0) = M x y := by
  let A : Matrix X X ℝ := fun x z => M x (e z)
  have hA : A ∈ doublyStochastic ℝ X := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun x z => hM x (e z), ?_, fun z => hcol (e z)⟩
    intro x
    dsimp only [A]
    rw [Equiv.sum_comp e]
    exact hrow x
  obtain ⟨w, hw, ht, he⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hA
  refine ⟨⟨w, hw, ht⟩, ?_⟩
  intro x y
  have hh := congrArg (fun B : Matrix X X ℝ => B x (e.symm y)) he
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, A, Equiv.apply_symm_apply, mul_ite, mul_one, mul_zero] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro σ _
  simp only [← Equiv.eq_symm_apply]

end Oberwolfach
