module

public import Oberwolfach.LongReferenceHostMargin

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

/-- A single reference density threshold satisfies both the matching and
parent-event bounds, with all choices made after the original constants. -/
theorem long_reference_matching_pstar_choice
    (ρ₀ tstar M:ℝ) (hρ₀:0<ρ₀) (ht:0<tstar) (hM:0<M) :
    ∃ pstar:ℝ,0<pstar ∧ 4*M*pstar≤ρ₀*(1/100) ∧ pstar≤ρ₀*tstar/4 := by
  let pstar:=min (ρ₀/(400*M)) (ρ₀*tstar/4)
  refine ⟨pstar,by dsimp [pstar];positivity,?_,min_le_right _ _⟩
  have hle:pstar≤ρ₀/(400*M):=min_le_left _ _
  have hmul:=mul_le_mul_of_nonneg_left hle (show 0≤4*M by positivity)
  have hden:400*M≠0:=by positivity
  have heq:4*M*(ρ₀/(400*M))=ρ₀*(1/100):=by field_simp;ring
  linarith
end Oberwolfach
