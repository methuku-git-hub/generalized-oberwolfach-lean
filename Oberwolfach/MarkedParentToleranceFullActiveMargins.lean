module

public import Oberwolfach.MarkedParentToleranceForActiveTransfer

@[expose] public section
/-! After the vortex ratio is fixed, the parent tolerance can also be made
small enough for the actual weighted first-active load transfer. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_parent_tolerance_full_active_margins
    (r:ℕ) (βA βrec cycleCoeff pathCoeff ζCfg tstar upper eta Cwide:ℝ)
    (hζ:0<ζCfg) (ht:0<tstar) (hupper:0<upper) (hη:0<eta) (hC:0≤Cwide)
    (hβ:βrec≤βA) (hcycle:3*βA≤cycleCoeff-(r+5:ℕ)*ζCfg)
    (hpath:3*βA≤pathCoeff-(r+4:ℕ)*ζCfg):
    ∃δparent:ℝ,0<δparent ∧ δparent≤upper ∧ 2*δparent≤ζCfg ∧
      δparent+δparent≤tstar/16 ∧ δparent+δparent+Cwide*δparent≤eta/8 ∧
      3*βrec≤cycleCoeff-(r+5:ℕ)*(2*δparent) ∧
      3*βrec≤pathCoeff-(r+4:ℕ)*(2*δparent) :=by
  let bound:ℝ:=min upper (eta/(8*(2+Cwide)))
  have hden:0<8*(2+Cwide):=by positivity
  have hbound:0<bound:=by dsimp [bound]; positivity
  obtain ⟨δ,hδ,hδbound,hcfg,hrow,hcycle',hpath'⟩:=
    marked_parent_tolerance_for_active_transfer r βA βrec cycleCoeff pathCoeff ζCfg tstar bound hζ ht hbound hβ hcycle hpath
  have hδupper:δ≤upper:=hδbound.trans (min_le_left _ _)
  have hδwide:δ≤eta/(8*(2+Cwide)):=hδbound.trans (min_le_right _ _)
  have hscaled:= (le_div_iff₀ hden).mp hδwide
  refine ⟨δ,hδ,hδupper,hcfg,hrow,?_,hcycle',hpath'⟩
  nlinarith only [hscaled]
end Oberwolfach
