module

public import Oberwolfach.LongReservedListOrderedParameters

@[expose] public section
/-! The list coefficient in the named parent event is exactly the coefficient
selected from the outer host parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reserved_outer_reference_alignment
    (αHost αRef ρ₀ βRaw βE εQ:ℝ) (m:ℕ)
    (hα:αRef=αHost/2)
    (hβ:βRaw=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)
    (hE:βE=βRaw/2) (hε:εQ≤βRaw/32) (htrim:1/(100*(m:ℝ))≤βE/8):
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16
    βList=βRaw ∧ εQ≤βList/32 ∧ 1/(100*(m:ℝ))≤βList/16 ∧ βList/2=βE := by
  have ha:2*αRef=αHost:=by linarith
  have hb:(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16=βRaw:=by rw [ha,hβ]
  dsimp only
  refine ⟨hb,?_,?_,?_⟩
  · simpa only [hb] using hε
  · rw [hb]
    rw [hE] at htrim
    linarith
  · simpa only [hb] using hE.symm
end Oberwolfach
