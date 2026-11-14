module

public import Oberwolfach.CommonEvents

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_positive_lower_bound_witness
    {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (Good:Ω→Prop) (b:ℝ)
    (hb:0<b) (hprob:b≤μ.probability Good):
    ∃z,0<μ.mass z ∧ Good z :=by
  have hp:0<μ.probability Good:=lt_of_lt_of_le hb hprob
  have hnonneg (z:Ω) (_:z∈Finset.univ):0≤(if Good z then μ.mass z else 0):=by
    split_ifs <;> simp_all [μ.nonneg z]
  have heq:μ.probability Good=∑z,(if Good z then μ.mass z else 0):=by
    unfold FiniteLaw.probability
    rfl
  rw [heq] at hp
  obtain ⟨z,_,hz⟩:=(Finset.sum_pos_iff_of_nonneg hnonneg).mp hp
  split_ifs at hz with hGood
  · exact ⟨z,hz,hGood⟩
  · linarith
end Oberwolfach
