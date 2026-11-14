module

public import Oberwolfach.FirstVortexInitialVortexReserveHierarchy

@[expose] public section
/-! The early cycle length can be chosen to absorb the list-trimming loss. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_trim_length (αRef ρ₀:ℝ) (hα:0<αRef) (hρ:0<ρ₀):
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃M:ℕ, ∀m:ℕ, M≤m → 1≤m → 1/(100*(m:ℝ))≤βList/16 :=by
  intro βList
  have hβ:0<βList:=by dsimp [βList]; positivity
  obtain ⟨M,hM⟩:=exists_nat_ge (16/βList)
  refine ⟨M,?_⟩
  intro m hm hm1
  have hmR:(0:ℝ)<m:=by exact_mod_cast hm1
  have hMm:(M:ℝ)≤m:=by exact_mod_cast hm
  have hmul:16≤βList*(m:ℝ):=by
    have hh:16/βList≤(m:ℝ):=hM.trans hMm
    simpa only [mul_comm] using (div_le_iff₀ hβ).mp hh
  apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(m:ℝ))).2
  nlinarith
end Oberwolfach
