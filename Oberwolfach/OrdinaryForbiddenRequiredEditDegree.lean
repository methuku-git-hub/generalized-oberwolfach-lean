module

public import Oberwolfach.OrdinaryRequiredAvoidsForbidden
public import Oberwolfach.OrdinaryProtectedRequiredDegree

@[expose] public section
/-! The original symmetric edit, the protected reservoir, the inner set and
forbidden graph together control the required and deleted degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem ordinary_forbidden_required_degree_bounds_of_edit
    (Target Sample Reference Protect Bad : SimpleGraph V) (Inner : Finset V) (b a f : ℝ)
    (hEdit : ∀ v, ((Finset.univ.filter (fun w => Xor (Target.Adj v w) (Sample.Adj v w))).card : ℝ) ≤ b)
    (hProtect : ∀ v, (Protect.degree v : ℝ) ≤ a)
    (hBad : ∀ v, (Bad.degree v : ℝ) ≤ f) :
    (∀ v, ((ordinaryForbiddenRequired Target Sample Reference Bad Inner).degree v : ℝ) ≤ b + Inner.card + f) ∧
    (∀ v, ((ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner).degree v : ℝ) ≤ b + a + Inner.card + f) := by
  have hp := ordinary_protected_required_degree_bounds Target Sample Reference Protect Inner b a hEdit hProtect
  constructor <;> intro v
  · have hd := (ordinary_forbidden_required_degree_bounds Target Sample Reference Protect Bad Inner v).1
    have hd' : ((ordinaryForbiddenRequired Target Sample Reference Bad Inner).degree v : ℝ) ≤
        (ordinaryProtectedRequired Target Sample Reference Inner).degree v + Bad.degree v := by
      exact_mod_cast hd
    linarith [hp.1 v, hBad v]
  · have hd := (ordinary_forbidden_required_degree_bounds Target Sample Reference Protect Bad Inner v).2
    have hd' : ((ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner).degree v : ℝ) ≤
        (ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner).degree v + Bad.degree v := by
      exact_mod_cast hd
    linarith [hp.2 v, hBad v]
end Oberwolfach
