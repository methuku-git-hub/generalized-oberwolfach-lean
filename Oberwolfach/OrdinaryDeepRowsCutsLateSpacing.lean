module

public import Oberwolfach.OrdinaryDeepRowsCutsChooseSpacing

@[expose] public section
/-! Apply the previously fixed deep tolerance after the parent selector has
revealed its additional positive vortex-error cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_rows_cuts_late_spacing
    (m K:ℕ) (α ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap capξ:ℝ)
    (hβchoose:∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤ε₀ ∧ β≤capξ ∧ β≤betaCap ∧ ξ+2*β<ηHub)
    (hdeep:OrdinaryDeepRowsCutsAfterParameters m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap)
    (d:ℕ) (hd:2≤d) (betaCap:ℝ) (hBetaCap:0<betaCap):
    ∃β:ℝ,0<β ∧ β≤betaCap ∧ ∃v₀:ℕ,1≤v₀ ∧
      OrdinaryDeepRowsCutsAfterSpacing m K d hd v₀ β α ρ₀ pmin αcut c C a ε₀ ρ θdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap :=by
  obtain ⟨β,hβ,hβ1,hβα,hβε,hβcap,hβlate,hgap⟩:=hβchoose betaCap hBetaCap
  obtain ⟨v₀,hv₀,hafter⟩:=ordinary_deep_rows_cuts_choose_spacing m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep
    aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap hdeep d hd β hβ.le hβ1 hβα hβε hgap
  exact ⟨β,hβ,hβlate,v₀,hv₀,hafter⟩
end Oberwolfach
