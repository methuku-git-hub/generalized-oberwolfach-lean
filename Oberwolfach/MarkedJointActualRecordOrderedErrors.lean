module

public import Oberwolfach.MarkedJointRecordOrderedErrorChoices
public import Oberwolfach.SuccessorPreweightExistence

@[expose] public section
/-! Substitute the exact fixed parent and active weight coefficients used
by the common event before selecting the record error margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_joint_actual_record_ordered_error_choices
    (r k₀:ℕ) (α ρ₀ sstar tstar kstar κ thetaDeep η x cap:ℝ)
    (hα:0<α) (hρ:0<ρ₀) (hs:0<sstar) (ht:0<tstar) (hk:0<kstar)
    (hκ:0<κ) (hθ:0<thetaDeep) (hη:0<η) (hx:0<x) (hcap:0<cap):
    let pstarLocal:=ρ₀*sstar/(2*((r+4:ℕ):ℝ))
    let Cparent:=11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))
    let Clocal:=5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1));
    ∃ ζCut deltaI hIcut:ℝ,
      0<ζCut ∧ ζCut≤cap ∧ ζCut≤tstar/16 ∧
      0<deltaI ∧ deltaI<1/4 ∧ 0<hIcut ∧
      deltaI≤(α/2)/32 ∧ deltaI≤kstar/32 ∧ 2*deltaI≤tstar/8 ∧
      2*hIcut≤(α/2)*kstar/4 ∧ 2*hIcut≤tstar/8-ζCut ∧
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
  intro pstarLocal Cparent Clocal
  have hp:0<pstarLocal:=by dsimp [pstarLocal];positivity
  have hu:0<successorWeightUpper k₀ (α/4):=(successorWeightConstants_pos k₀ (α/4) (by positivity)).2
  have hCp:0≤Cparent:=by dsimp [Cparent];positivity
  have hCl:0≤Clocal:=by dsimp [Clocal];positivity
  exact marked_joint_record_ordered_error_choices r (α/2) kstar tstar κ thetaDeep η x Cparent Clocal cap
    (by positivity) hk ht hκ hθ hη hx hCp hCl hcap
end Oberwolfach
