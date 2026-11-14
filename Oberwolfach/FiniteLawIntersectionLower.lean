module

public import Oberwolfach.CommonEvents

@[expose] public section
/-! Intersect two events without an independence assumption. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_intersection_lower
    {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (A B:Ω→Prop) (a b:ℝ)
    (hA:1-a≤μ.probability A) (hB:1-b≤μ.probability B):
    1-a-b≤μ.probability (fun x=>A x ∧ B x):=by
  have ha:μ.probability (fun x=>¬A x)≤a:=by have h:=finiteLaw_probability_compl μ A;linarith
  have hb:μ.probability (fun x=>¬B x)≤b:=by have h:=finiteLaw_probability_compl μ B;linarith
  have hh:=finiteLaw_common_event_lower μ (Finset.univ:Finset Bool)
    (fun i x=>if i then ¬A x else ¬B x) (fun i=>if i then a else b)
    (by intro i hi;cases i <;> simp_all)
  simpa [Fintype.sum_bool, and_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hh
end Oberwolfach
