module

public import Oberwolfach.OrdinaryFinishInputsFromSchedule

@[expose] public section
/-! Name the already checked completion inequalities so they can be
passed between the parameter selector and the per-host certificate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryAsymmetricFinishSchedule
    (m Nfinish:ℕ) (eParent hParent ε βe βh θmatch p δsample ellCap finishCap kcap rate ν cap:ℝ):Prop:=
  ∀n:ℕ,Nfinish≤n→2≤θmatch*p*n/4 ∧
    ∃Kcap Dmax:ℕ,0<Kcap ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤kcap^2*n ∧
    ∀τ ηrate ellrate Lconf:ℝ,0≤τ→τ≤cap→0≤ηrate→ηrate≤finishCap→0≤ellrate→ellrate≤ellCap→
      Lconf≤kcap^2*n→
      (βe*n+3*max (ηrate*n) (ellrate*n)≤(eParent*ε)*n ∧
       βh*n+2*(ellrate*n)≤(hParent*ε)*n) ∧
      (τ+ν≤p^2/4 ∧ τ+ν+(p*ellrate+δsample)≤θmatch*p/4 ∧ ν+ηrate≤θmatch*p/4) ∧
      (((n*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
        (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((Kcap+Dmax:ℕ):ℝ))+
        (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*(ν*n) ∧
       ν*n+ηrate*n+2*((2*p)*n)+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*n)
end Oberwolfach
