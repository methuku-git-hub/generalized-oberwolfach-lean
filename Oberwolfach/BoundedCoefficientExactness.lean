module

public import Oberwolfach.ApproximateConvexMembership

@[expose] public section

/-! The bounded-coefficient separation lemma, including the subspace in which
nearby targets are quantified. No approximate representation is assumed outside
that subspace. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def finiteCombinationMap {I E : Type*} [Fintype I] [AddCommGroup E] [Module ℝ E]
    (P : I → E) : (I → ℝ) →ₗ[ℝ] E where
  toFun := fun a => ∑ i, a i • P i
  map_add' a μ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a a := by simp [mul_smul, Finset.smul_sum]

theorem bounded_coefficients_exact
    {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (P : I → E) (w : E) (B κ ε : ℝ)
    (hκ : 0 < κ) (hεκ : ε < κ)
    (happrox : ∀ w' : E, ‖w' - w‖ ≤ κ → ∃ a : I → ℝ,
      (∀ i, 0 ≤ a i ∧ a i ≤ B) ∧ ‖(∑ i, a i • P i) - w'‖ ≤ ε) :
    ∃ a : I → ℝ, (∀ i, 0 ≤ a i ∧ a i ≤ B) ∧ (∑ i, a i • P i) = w := by
  let T := finiteCombinationMap P
  let Z := T '' Set.Icc (0 : I → ℝ) (fun _ => B)
  have hc : Convex ℝ Z := (convex_Icc (0 : I → ℝ) (fun _ => B)).linear_image T
  have hk : IsCompact Z := isCompact_Icc.image T.continuous_of_finiteDimensional
  have hw : w ∈ Z := exact_membership_of_nearby_approximations Z hc hk.isClosed w κ ε hκ hεκ (by
    intro w' hw'
    obtain ⟨a,ha,he⟩ := happrox w' hw'
    refine ⟨T a, ?_, he⟩
    exact ⟨a, ⟨fun i => (ha i).1, fun i => (ha i).2⟩, rfl⟩)
  obtain ⟨a,ha,hT⟩ := hw
  exact ⟨a, fun i => ⟨ha.1 i,ha.2 i⟩, hT⟩

theorem subspace_bounded_coefficients_exact
    {I E : Type*} [Fintype I] [Fintype E]
    (S : Submodule ℝ (E → ℝ)) (P : I → E → ℝ) (hP : ∀ i, P i ∈ S)
    (w : E → ℝ) (hw : w ∈ S) (B κ ε : ℝ) (hκ : 0 < κ) (hεκ : ε < κ)
    (happrox : ∀ w' ∈ S, ‖w' - w‖ ≤ κ → ∃ a : I → ℝ,
      (∀ i, 0 ≤ a i ∧ a i ≤ B) ∧ ‖(∑ i, a i • P i) - w'‖ ≤ ε) :
    ∃ a : I → ℝ, (∀ i, 0 ≤ a i ∧ a i ≤ B) ∧ (∑ i, a i • P i) = w := by
  let p : I → S := fun i => ⟨P i,hP i⟩
  let v : S := ⟨w,hw⟩
  obtain ⟨a,ha,hT⟩ := bounded_coefficients_exact p v B κ ε hκ hεκ (by
    intro v' hv'
    obtain ⟨a,ha,he⟩ := happrox v'.val v'.property hv'
    refine ⟨a,ha,?_⟩
    change ‖(((∑ i, a i • p i) - v' : S) : E → ℝ)‖ ≤ ε
    simpa [p] using he)
  refine ⟨a,ha,?_⟩
  have hh := congrArg (fun z : S => z.val) hT
  simpa [p,v] using hh

end Oberwolfach
