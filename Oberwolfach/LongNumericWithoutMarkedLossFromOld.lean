module

public import Oberwolfach.LongReservedListUniformNumericBudgets

@[expose] public section
/-! The previously selected constants already satisfy the improved list
budget. The inverse-length premise can be avoided by using the harmless
zero index in the old universal arithmetic statement. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_numeric_without_marked_loss_from_old
    (n d:ℕ) (αHost ρ₀ lamEarly ζEarly ηListEarly:ℝ) (hη:0≤ηListEarly)
    (hNumeric:let βList:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
      βList*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*(1/100:ℝ) ∧
      (lamEarly+2*ζEarly)*n≤βList*n ∧ (n:ℝ)^(3/4:ℝ)≤ηListEarly*n ∧
      ∀(m:ℕ) (ε:ℝ),ε≤βList/32→1/(100*(m:ℝ))≤βList/16→
        βList/2+ε+1/(100*(m:ℝ))+ηListEarly≤lamEarly)
    (hβ:0≤(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16):
    let βList:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
      βList*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*(1/100:ℝ) ∧
      (lamEarly+2*ζEarly)*n≤βList*n ∧ (n:ℝ)^(3/4:ℝ)≤ηListEarly*n ∧
      ∀ε:ℝ,ε≤βList/32→βList/2+ε≤lamEarly:=by
  dsimp only at hNumeric ⊢
  obtain ⟨herror,hmargin,hbudget,hsub,htrim⟩:=hNumeric
  refine ⟨herror,hmargin,hbudget,hsub,?_⟩
  intro ε hε
  have hh:=htrim 0 ε hε (by simpa using (div_nonneg hβ (by norm_num : (0:ℝ)≤16)))
  norm_num at hh
  linarith
end Oberwolfach
