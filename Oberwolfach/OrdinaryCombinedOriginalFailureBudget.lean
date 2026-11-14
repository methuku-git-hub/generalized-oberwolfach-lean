module

public import Oberwolfach.OrdinaryReservoirFailureBudget

@[expose] public section
/-! The matching, reference-balance, reserved-test and constructed-reservoir
losses fit the original failure allowance and its n^-10 tail. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_combined_original_failure_budget (χ:ℝ) (hχ:0<χ):
    ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀εE ζ χpair χlist χbal χbd χnbr χpairR χpath:ℝ,
      εE≤χ/32→ζ≤χ/32→χpair≤χ/32→χlist≤χ/32→χbal≤χ/32→χbd≤χ/32→χnbr≤χ/32→χpairR≤χ/32→χpath≤χ/32→
      (((((((εE+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath)+
        (2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2))≤χ+1/(n:ℝ)^10 :=by
  obtain ⟨N,hN,hr⟩:=ordinary_reservoir_failure_budget (χ/2) (by positivity)
  refine ⟨N,hN,?_⟩
  intro n hn εE ζ χpair χlist χbal χbd χnbr χpairR χpath hE hζ hp hl hb hbd hnbr hpR hpath
  have hres:=hr n hn
  linarith
end Oberwolfach
