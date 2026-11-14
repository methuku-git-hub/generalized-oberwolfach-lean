module

public import Mathlib.Tactic

@[expose] public section
/-! The no-new-spoke property and the measured loss on the first inner set
control each hub column, including hubs outside the inner hub set. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_inner_spoke_column_from_correction
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (A:Finset V) (H H':Bool→V→U→Prop) (δ:ℝ) (hδ:0≤δ)
    (hmark:∀v u,H true v u↔H' true v u)
    (hnoNew:∀u v,v∈A→H' false v u→H false v u)
    (hloss:∀u,((A.filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤δ):
    ∀b u,(∑v∈A,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)≤δ :=by
  intro b u
  cases b with
  | true =>
    have hz:(∑v∈A,if ¬(H true v u↔H' true v u) then (1:ℝ) else 0)=0:=by
      apply Finset.sum_eq_zero
      intro v hv
      simp [hmark v u]
    simpa only [hz] using hδ
  | false =>
    have hpoint:∀v∈A,(if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤
        if H false v u ∧ ¬H' false v u then 1 else 0:=by
      intro v hv
      have hh:=hnoNew u v hv
      by_cases ho:H false v u <;> by_cases hn:H' false v u <;> simp_all
    calc
      _ ≤ ∑v∈A,if H false v u ∧ ¬H' false v u then (1:ℝ) else 0 := Finset.sum_le_sum hpoint
      _ = ((A.filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ) := by
        simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ δ := hloss u
end Oberwolfach
