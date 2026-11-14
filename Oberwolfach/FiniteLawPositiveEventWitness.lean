module

public import Oberwolfach.FiniteLawManyGoodEvents

@[expose] public section
/-! A positive-probability finite event contains a positive-mass outcome. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_positive_mass_witness_of_event {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (E:Ω→Prop) (h:0<μ.probability E):
    ∃ω,0<μ.mass ω ∧ E ω:=by
  have hn:∀ω∈(Finset.univ:Finset Ω),0≤(if E ω then μ.mass ω else 0):=by
    intro ω _
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl
  have heq:μ.probability E=∑ω,(if E ω then μ.mass ω else 0):=by
    unfold FiniteLaw.probability
    apply Finset.sum_congr rfl
    intro ω _
    exact (ite_eq_ite (E ω) (μ.mass ω) 0).mpr trivial
  rw [heq] at h
  obtain ⟨ω,_,hw⟩:=(Finset.sum_pos_iff_of_nonneg hn).mp h
  split_ifs at hw with hE
  · exact ⟨ω,hw,hE⟩
  · exact (lt_irrefl _ hw).elim
end Oberwolfach
