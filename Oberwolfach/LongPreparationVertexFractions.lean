module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! Frequencies of short and long components obtained from actual vertices. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_vertex_fractions {V:Type*} [Fintype V] [DecidableEq V]
    (hV:0<Fintype.card V) (K:ℕ) (classify:V→Option (Fin K)):
    let fraction:Option (Fin K)→ℝ:=fun j=>
      ((Finset.univ.filter (fun v=>classify v=j)).card:ℝ)/(Fintype.card V:ℝ)
    (∀ j,0≤fraction j) ∧ fraction none+(∑ i,fraction (some i))=1:=by
  intro fraction
  have hcard:(0:ℝ)<Fintype.card V:=by exact_mod_cast hV
  have hsum : (∑ j:Option (Fin K), (Finset.univ.filter (fun v=>classify v=j)).card)=Fintype.card V:=by
    simpa using (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ:Finset V)
      (Finset.univ:Finset (Option (Fin K))) classify)
  have hsumR:(∑ j:Option (Fin K), ((Finset.univ.filter (fun v=>classify v=j)).card:ℝ))=Fintype.card V:=by
    exact_mod_cast hsum
  have hnorm:(∑ j:Option (Fin K),fraction j)=1:=by
    simp only [fraction, ← Finset.sum_div,hsumR]
    exact div_self (ne_of_gt hcard)
  refine ⟨?_,?_⟩
  · intro j
    dsimp [fraction]
    positivity
  · simpa only [Fintype.sum_option] using hnorm
end Oberwolfach
