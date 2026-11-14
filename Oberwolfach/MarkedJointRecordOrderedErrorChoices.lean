module

public import Oberwolfach.MarkedJointRecordErrorChoice
public import Oberwolfach.MarkedUniformCutRecordChoice

@[expose] public section
/-! Choose the cut geometry before the balance tolerance; the latter is
returned by the cover-down theorem only after the cut parameters are fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_joint_record_ordered_error_choices
    (r:ℕ) (α kstar tstar κ thetaDeep η x Cparent Clocal cap:ℝ)
    (hα:0<α) (hk:0<kstar) (ht:0<tstar) (hκ:0<κ) (hθ:0<thetaDeep)
    (hη:0<η) (hx:0<x) (hCp:0≤Cparent) (hCl:0≤Clocal) (hcap:0<cap):
    ∃ ζCut deltaI hIcut:ℝ,
      0<ζCut ∧ ζCut≤cap ∧ ζCut≤tstar/16 ∧
      0<deltaI ∧ deltaI<1/4 ∧ 0<hIcut ∧
      deltaI≤α/32 ∧ deltaI≤kstar/32 ∧ 2*deltaI≤tstar/8 ∧
      2*hIcut≤α*kstar/4 ∧ 2*hIcut≤tstar/8-ζCut ∧
      ∀ etaBal:ℝ,0<etaBal→
      ∃ tolRef ζActive τParent tolParent ζParent τ tolLocal ζLocal rowErr ζRow epsBal ζBal:ℝ,
        0<tolRef ∧ tolRef≤cap ∧ 0<ζActive ∧ ζActive≤cap ∧
        tolRef+(r+12:ℕ)*ζActive≤κ/4 ∧ tolRef+(r+12:ℕ)*ζActive≤x/2 ∧ ζActive≤κ/4 ∧
        0<τParent ∧ τParent≤cap ∧ 0<tolParent ∧ tolParent≤cap ∧ 0<ζParent ∧ ζParent≤cap ∧
        τParent+tolParent+Cparent*ζParent≤κ/4 ∧ τParent+tolParent+Cparent*ζParent≤thetaDeep/4 ∧
        0<τ ∧ τ≤cap ∧ 0<tolLocal ∧ tolLocal≤cap ∧ τ+tolLocal≤η/8 ∧
        0<ζLocal ∧ ζLocal≤cap ∧ τ+tolLocal+Clocal*ζLocal≤η/4 ∧
        0<rowErr ∧ rowErr≤cap ∧ 0<ζRow ∧ ζRow≤cap ∧ rowErr+ζRow≤tstar/8 ∧
        0<epsBal ∧ epsBal≤cap ∧ 0<ζBal ∧ ζBal≤cap ∧
        epsBal+((r+4)+2:ℕ)*ζBal≤etaBal ∧ epsBal+((r+4)+2:ℕ)*ζBal≤x/2 ∧
        ∀ ε Cwide:ℝ,0<ε→0≤Cwide→∃ ζWide:ℝ,0<ζWide ∧ ζWide≤cap ∧
          τ+tolLocal+Cwide*(4/ε)*ζWide≤η/4:=by
  let ζCut:=min cap (tstar/32)
  have hz:0<ζCut:=by dsimp [ζCut];positivity
  have hzcap:ζCut≤cap:=min_le_left _ _
  have hzsmall:ζCut≤tstar/16:=by have hh:ζCut≤tstar/32:=min_le_right _ _;linarith
  obtain ⟨deltaI,hIcut,hδ,hδcap,hi,hicap,hδα,hδk,hδt,hiprod,hispoke⟩:=
    marked_uniform_inner_cut_record_choice α kstar tstar ζCut (1/8) cap hα hk ht hzsmall (by norm_num) hcap
  refine ⟨ζCut,deltaI,hIcut,hz,hzcap,hzsmall,hδ,by linarith,hi, hδα,hδk,hδt,hiprod,hispoke,?_⟩
  intro etaBal hbal
  exact marked_joint_record_error_choice r (r+4) κ thetaDeep η etaBal x tstar Cparent Clocal cap
    hκ hθ hη hbal hx ht hCp hCl hcap
end Oberwolfach
