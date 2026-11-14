module

public import Oberwolfach.OrdinaryCleanupProfileInflateEdit

@[expose] public section
/-! Pick fixed event margins before the later actual edit. The resulting
slack absorbs any edit envelope bounded at the vortex's inner scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_edit_envelope_margin_choices
    (eParent hParent:ℝ) (he:0<eParent) (hh:0<hParent):
    ∃eEvent hEvent cap:ℝ,0<eEvent ∧ 0<hEvent ∧ 0<cap ∧
      eEvent≤eParent ∧ hEvent≤hParent ∧
    ∀ε n inner Lold Lnew:ℝ,0≤ε→0≤n→0≤ inner→0≤Lold→Lold≤Lnew→
      inner≤ε*n→Lnew≤cap*inner→
      (eEvent*ε)*n+3*Lnew≤(eParent*ε)*n+3*Lold ∧
      (hEvent*ε)*n+2*Lnew≤(hParent*ε)*n+2*Lold:=by
  let eEvent:ℝ:=eParent/2
  let hEvent:ℝ:=hParent/2
  let cap:ℝ:=min (eParent/12) (hParent/8)
  have heEvent:0<eEvent:=by dsimp [eEvent];positivity
  have hhEvent:0<hEvent:=by dsimp [hEvent];positivity
  have hcap:0<cap:=by dsimp [cap];positivity
  have hcapE:cap≤eParent/12:=min_le_left _ _
  have hcapH:cap≤hParent/8:=min_le_right _ _
  have hcoefE:eEvent+3*cap≤eParent:=by dsimp [eEvent];linarith
  have hcoefH:hEvent+2*cap≤hParent:=by dsimp [hEvent];linarith
  refine ⟨eEvent,hEvent,cap,heEvent,hhEvent,hcap,by dsimp [eEvent];linarith,
    by dsimp [hEvent];linarith,?_⟩
  intro ε n inner Lold Lnew hε hn hinner hLold hL hinnerCap hLnew
  have hLbound:Lnew≤cap*(ε*n):=hLnew.trans (mul_le_mul_of_nonneg_left hinnerCap hcap.le)
  have hE:=mul_le_mul_of_nonneg_right hcoefE (mul_nonneg hε hn)
  have hH:=mul_le_mul_of_nonneg_right hcoefH (mul_nonneg hε hn)
  constructor <;> nlinarith only [hLbound,hE,hH,hLold]
end Oberwolfach
