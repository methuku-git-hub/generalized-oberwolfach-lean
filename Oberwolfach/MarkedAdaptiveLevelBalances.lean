module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! The four density identities at a level reduce to two centre equalities. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Oberwolfach

theorem marked_adaptive_level_balances
    (ρ s₀ m Dbal Dload B H:ℝ) (hm:0<m)
    (hcentre:(ρ*s₀/2)*Dbal=s₀*B)
    (hload:H*s₀=Dload*(ρ*s₀/2)):
    (ρ*(s₀/m)/2)*Dbal=(s₀/m)*B ∧
    H*(s₀/m)=Dload*(ρ*(s₀/m)/2) ∧
    H*(s₀/m)*m=Dload*(ρ*s₀/2) := by
  have hcentre':=((congrArg (fun x:ℝ=>x/m) hcentre))
  have hload':=((congrArg (fun x:ℝ=>x/m) hload))
  refine ⟨?_,?_,?_⟩
  · convert hcentre' using 1 <;> ring
  · convert hload' using 1 <;> ring
  · have hm0:m≠0:=ne_of_gt hm
    field_simp
    nlinarith only [hload]
end Oberwolfach
