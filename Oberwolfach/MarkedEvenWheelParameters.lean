module

public import Oberwolfach.MarkedWheels
public import Oberwolfach.SuccessorCyclicMargin

@[expose] public section
/-! The marked-wheel index `m` counts ordinary rim arcs; the wheel has
`m+1` rim edges. The even wheel length used in marked completion can
therefore be written as `r+5` with the reference-event parameter `r` odd. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_even_wheel_reference_parameters (c:ℕ) (hc:Even c) (hc8:8≤c):
    ∃ r k₀:ℕ,3≤r ∧ Odd r ∧ c=r+5 ∧ r+4+1=(k₀+2)*2:=by
  obtain ⟨q,hq⟩:=hc
  refine ⟨c-5,q-2,?_,?_,?_,?_⟩
  · omega
  · apply Nat.not_even_iff_odd.mp
    intro hr
    obtain ⟨k,hk⟩:=hr
    omega
  · omega
  · omega

theorem marked_r_one_rim_cardinality:Fintype.card (Fin ((1:ℕ)+4+1))=6:=by
  simp
/-- A single threshold makes both the parity and successor-density margin
available for every sufficiently large even wheel length. -/
theorem marked_even_wheel_parameters_with_successor_margin (α:ℝ) (hα:0<α):
    ∃ c₀:ℕ,8≤c₀ ∧ ∀ c:ℕ,c₀≤c→Even c→
      ∃ r k₀:ℕ,3≤r ∧ Odd r ∧ c=r+5 ∧ r+4+1=(k₀+2)*2 ∧
        successorCycleRatio k₀+α/4≤1/2+α/2:=by
  let c₀:ℕ:=⌈2/α⌉₊+8
  refine ⟨c₀,by dsimp [c₀];omega,?_⟩
  intro c hc hEven
  have hc8:8≤c:=by dsimp [c₀] at hc;omega
  obtain ⟨r,k₀,hr,hodd,hcR,hlen⟩:=marked_even_wheel_reference_parameters c hEven hc8
  refine ⟨r,k₀,hr,hodd,hcR,hlen,?_⟩
  have hcScale:(2/α:ℝ)+8≤c:=by
    have ha:(2/α:ℝ)≤⌈2/α⌉₊:=Nat.le_ceil _
    have hb:((⌈2/α⌉₊:ℕ):ℝ)+8≤c:=by exact_mod_cast hc
    linarith
  have hcEq:(c:ℝ)=2*((k₀:ℝ)+2):=by
    have hh:c=(k₀+2)*2:=by omega
    exact_mod_cast hh.trans (Nat.mul_comm (k₀+2) 2)
  have hd:0<2*((k₀:ℝ)+2)-1:=by
    have hk:0≤(k₀:ℝ):=Nat.cast_nonneg _
    linarith
  have hmul:2≤α*(2*((k₀:ℝ)+2)-1):=by
    have hc':(2:ℝ)/α≤(c:ℝ)-8:=by linarith [hcScale]
    have hh:2≤((c:ℝ)-8)*α:=(div_le_iff₀ hα).mp hc'
    rw [hcEq] at hh
    nlinarith
  unfold successorCycleRatio
  have hh:((k₀:ℝ)+2)/(2*((k₀:ℝ)+2)-1)≤1/2+α/4:=by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  linarith

end Oberwolfach
