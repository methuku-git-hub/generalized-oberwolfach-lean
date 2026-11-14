module

public import Oberwolfach.BoundedCoefficientExactness

@[expose] public section

/-! A uniform positive preliminary weighting is retained when approximate
representations are made exact on the balanced subspace. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem subspace_positive_bounded_coefficients
    {I E : Type*} [Fintype I] [Fintype E]
    (S : Submodule ℝ (E → ℝ)) (P : I → E → ℝ) (hP : ∀ i,P i∈S)
    (center w : E → ℝ) (hw : w∈S)
    (κ ε B b : ℝ) (hκ : 0<κ) (hb : 0<b) (hε : ε<κ/4)
    (hwclose : ‖w-center‖ ≤ κ/4)
    (hpre : ‖∑ i,b • P i‖ ≤ κ/4)
    (happrox : ∀ w'∈S,‖w'-center‖ ≤ κ → ∃ a : I → ℝ,
      (∀ i,0≤a i ∧ a i≤B) ∧ ‖(∑ i,a i • P i)-w'‖ ≤ ε) :
    ∃ a : I → ℝ,(∀ i,0<a i ∧ b≤a i ∧ a i≤b+B) ∧ (∑ i,a i • P i)=w := by
  let v := ∑ i,b • P i
  have hv : v∈S := S.sum_mem (fun i _ => S.smul_mem b (hP i))
  have hwv : w-v∈S := S.sub_mem hw hv
  obtain ⟨a,ha,he⟩ := subspace_bounded_coefficients_exact S P hP (w-v) hwv B (κ/4) ε
    (by positivity) hε (by
      intro w' hw' hclose
      apply happrox w' hw'
      have heq : w'-center=(w'-(w-v))+(w-center)-v := by abel
      rw [heq]
      have hn := (norm_sub_le ((w'-(w-v))+(w-center)) v).trans
        (add_le_add (norm_add_le (w'-(w-v)) (w-center)) (le_refl ‖v‖))
      have hvnorm : ‖v‖ ≤ κ/4 := hpre
      linarith)
  refine ⟨fun i => b+a i,?_,?_⟩
  · intro i
    exact ⟨by linarith [(ha i).1],by linarith [(ha i).1],by linarith [(ha i).2]⟩
  · simp only [add_smul,Finset.sum_add_distrib,he]
    change v+(w-v)=w
    abel

end Oberwolfach
