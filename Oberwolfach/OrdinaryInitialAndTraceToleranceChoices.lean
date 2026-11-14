module

public import Mathlib.Tactic

@[expose] public section
/-! Choose the initial correction tolerance independently of the earlier
later-trace tolerance, and fit both sample errors and the edit cap inside
all already selected positive allowances. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_initial_and_trace_tolerance_choices
    (δ ρ₀ rateParent capEvent ζlimit εsample δDeep δInitial δJoint δend:ℝ)
    (hδ:0<δ) (hρ₀:0<ρ₀) (hrate:0<rateParent) (hcap:0<capEvent)
    (hζ:0<ζlimit) (hsample:0<εsample) (hdeep:0<δDeep)
    (hinitial:0<δInitial) (hjoint:0<δJoint) (hend:0<δend):
    ∃ζInitial capEdit δcap εR εH:ℝ,
      0<ζInitial ∧ ζInitial≤δ ∧ ζInitial≤δ*(ρ₀/8) ∧ ζInitial≤rateParent ∧
      0<capEdit ∧ capEdit≤capEvent ∧ capEdit≤ζlimit ∧
      0<δcap ∧ δcap≤ζInitial/2 ∧ δcap≤capEdit/2 ∧
      0<εR ∧ εR≤δ ∧ εR≤εsample ∧ εR≤δDeep ∧ εR≤δInitial ∧ εR≤δJoint ∧ εR≤δend/4 ∧
      0<εH ∧ εH≤δ ∧ εH≤εsample ∧ εH≤δDeep ∧ εH≤δInitial ∧ εH≤δJoint ∧ εH≤δend/4 :=by
  let ζInitial:ℝ:=min δ (min (δ*(ρ₀/8)) rateParent)/2
  let capEdit:ℝ:=min capEvent ζlimit/2
  let δcap:ℝ:=min ζInitial capEdit/4
  let err:ℝ:=min δ (min εsample (min δDeep (min δInitial (min δJoint (δend/4)))))/2
  have hζInitial:0<ζInitial:=by dsimp [ζInitial];positivity
  have hcapEdit:0<capEdit:=by dsimp [capEdit];positivity
  have hδcap:0<δcap:=by dsimp [δcap];positivity
  have herr:0<err:=by dsimp [err];positivity
  have hζδ:ζInitial≤δ:=by
    have h:=min_le_left δ (min (δ*(ρ₀/8)) rateParent)
    dsimp [ζInitial];linarith
  have hζρ:ζInitial≤δ*(ρ₀/8):=by
    have h:=(min_le_right δ (min (δ*(ρ₀/8)) rateParent)).trans (min_le_left _ _)
    have hh:0≤δ*(ρ₀/8):=by positivity
    dsimp [ζInitial]
    linarith
  have hζrate:ζInitial≤rateParent:=by
    have h:=(min_le_right δ (min (δ*(ρ₀/8)) rateParent)).trans (min_le_right _ _)
    dsimp [ζInitial];linarith
  have hcapEvent:capEdit≤capEvent:=by
    have h:=min_le_left capEvent ζlimit;dsimp [capEdit];linarith
  have hcapLimit:capEdit≤ζlimit:=by
    have h:=min_le_right capEvent ζlimit;dsimp [capEdit];linarith
  have hδζ:δcap≤ζInitial/2:=by
    have h:=min_le_left ζInitial capEdit;dsimp [δcap];linarith
  have hδcap':δcap≤capEdit/2:=by
    have h:=min_le_right ζInitial capEdit;dsimp [δcap];linarith
  have herrδ:err≤δ:=by
    have h:=min_le_left δ (min εsample (min δDeep (min δInitial (min δJoint (δend/4)))))
    dsimp [err];linarith
  have herrSample:err≤εsample:=by
    have h:=(min_le_right δ (min εsample (min δDeep (min δInitial (min δJoint (δend/4)))))).trans (min_le_left _ _)
    dsimp [err];linarith
  have herrDeep:err≤δDeep:=by
    have h:min δ (min εsample (min δDeep (min δInitial (min δJoint (δend/4)))))≤δDeep:=((min_le_right δ _).trans (min_le_right εsample _)).trans (min_le_left δDeep _)
    dsimp [err];linarith
  have herrInitial:err≤δInitial:=by
    have h:min δ (min εsample (min δDeep (min δInitial (min δJoint (δend/4)))))≤δInitial:=(((min_le_right δ _).trans (min_le_right εsample _)).trans (min_le_right δDeep _)).trans (min_le_left δInitial _)
    dsimp [err];linarith
  have herrJoint:err≤δJoint:=by
    have h:min δ (min εsample (min δDeep (min δInitial (min δJoint (δend/4)))))≤δJoint:=((((min_le_right δ _).trans (min_le_right εsample _)).trans (min_le_right δDeep _)).trans (min_le_right δInitial _)).trans (min_le_left δJoint _)
    dsimp [err];linarith
  have herrEnd:err≤δend/4:=by
    have h:min δ (min εsample (min δDeep (min δInitial (min δJoint (δend/4)))))≤δend/4:=((((min_le_right δ _).trans (min_le_right εsample _)).trans (min_le_right δDeep _)).trans (min_le_right δInitial _)).trans (min_le_right δJoint _)
    dsimp [err];linarith
  exact ⟨ζInitial,capEdit,δcap,err,err,hζInitial,hζδ,hζρ,hζrate,
    hcapEdit,hcapEvent,hcapLimit,hδcap,hδζ,hδcap',
    herr,herrδ,herrSample,herrDeep,herrInitial,herrJoint,herrEnd,herr,herrδ,herrSample,herrDeep,herrInitial,herrJoint,herrEnd⟩
end Oberwolfach
