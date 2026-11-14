module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic

@[expose] public section

/-! A bijection preserving a specified class, obtained from equal class
sizes and equal total sizes. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

 theorem finite_bijection_preserving_predicate {X Y:Type*} [Fintype X] [Fintype Y]
    (P:X→Prop) (Q:Y→Prop) [DecidablePred P] [DecidablePred Q]
    (hcard:Fintype.card X=Fintype.card Y)
    (hclass:Fintype.card {x // P x}=Fintype.card {y // Q y}):
    ∃ e:X≃Y,∀ x,Q (e x)↔P x:=by
  let e₁:{x // P x}≃{y // Q y}:=Fintype.equivOfCardEq hclass
  let e₂:{x // ¬P x}≃{y // ¬Q y}:=Fintype.equivOfCardEq
    (by rw [Fintype.card_subtype_compl,Fintype.card_subtype_compl,hcard,hclass])
  let e: X≃Y:=(Equiv.sumCompl P).symm.trans ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl Q))
  refine ⟨e,?_⟩
  intro x
  by_cases hx:P x
  · have he:Q (e x):=by
      change Q ((Equiv.sumCompl Q) ((Equiv.sumCongr e₁ e₂) ((Equiv.sumCompl P).symm x)))
      rw [Equiv.sumCompl_symm_apply_of_pos hx]
      exact (e₁ ⟨x,hx⟩).property
    exact ⟨fun _=>hx,fun _=>he⟩
  · have he:¬Q (e x):=by
      change ¬Q ((Equiv.sumCompl Q) ((Equiv.sumCongr e₁ e₂) ((Equiv.sumCompl P).symm x)))
      rw [Equiv.sumCompl_symm_apply_of_neg hx]
      exact (e₂ ⟨x,hx⟩).property
    exact ⟨fun h=>(he h).elim,fun h=>(hx h).elim⟩

end Oberwolfach
