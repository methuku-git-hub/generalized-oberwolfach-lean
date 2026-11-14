module

public import Oberwolfach.MarkedJointRecordErrorChoice
public import Oberwolfach.MarkedParentLoadParameterChoice
public import Oberwolfach.MarkedActiveRowsLoadsParameterChoice
public import Oberwolfach.MarkedBalanceRecordMargins

@[expose] public section
/-! Compatible numerical margins for the sampled parent and active record
inputs. The larger-hub retention error remains chosen after the vortex ratio. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_joint_record_strict_error_choice
    (r c:ℕ) (κ thetaDeep η etaBal x tstar Cparent Clocal cap:ℝ)
    (hκ:0<κ) (hθ:0<thetaDeep) (hη:0<η) (hbal:0<etaBal) (hx:0<x)
    (ht:0<tstar) (hC:0≤Cparent) (hClocal:0≤Clocal) (hcap:0<cap):
    ∃ tolRef ζActive τParent tolParent ζParent τ tolLocal ζLocal rowErr ζRow epsBal ζBal:ℝ,
      0<tolRef ∧ tolRef≤cap ∧ 0<ζActive ∧ ζActive≤cap ∧
      tolRef+(r+12:ℕ)*ζActive≤κ/8 ∧ tolRef+(r+12:ℕ)*ζActive≤x/4 ∧ ζActive≤κ/8 ∧
      0<τParent ∧ τParent≤cap ∧ 0<tolParent ∧ tolParent≤cap ∧ 0<ζParent ∧ ζParent≤cap ∧
      τParent+tolParent+Cparent*ζParent≤κ/8 ∧ τParent+tolParent+Cparent*ζParent≤thetaDeep/8 ∧
      0<τ ∧ τ≤cap ∧ 0<tolLocal ∧ tolLocal≤cap ∧ τ+tolLocal≤η/16 ∧
      0<ζLocal ∧ ζLocal≤cap ∧ τ+tolLocal+Clocal*ζLocal≤η/8 ∧
      0<rowErr ∧ rowErr≤cap ∧ 0<ζRow ∧ ζRow≤cap ∧ rowErr+ζRow≤tstar/16 ∧
      0<epsBal ∧ epsBal≤cap ∧ 0<ζBal ∧ ζBal≤cap ∧
      epsBal+(c+2:ℕ)*ζBal≤etaBal/2 ∧ epsBal+(c+2:ℕ)*ζBal≤x/4 ∧
      ∀ ε Cwide:ℝ,0<ε→0≤Cwide→∃ ζWide:ℝ,0<ζWide ∧ ζWide≤cap ∧
        τ+tolLocal+Cwide*(4/ε)*ζWide≤η/8 :=by
  obtain ⟨tolRef,ζActive,τP,tolP,ζP,τ,tol,ζLocal,row,ζrow,eb,zb,
    htol,htolcap,hζ,hζcap,hκref,hxref,hζκ,hτP,hτPcap,htolP,htolPcap,hζP,hζPcap,hκP,hθP,
    hτ,hτcap,htolLocal,htcap,hbase,hζLocal,hζLocalCap,hlocal,hrow,hrowcap,hζrow,hζrowcap,hrowmargin,
    heb,hecap,hzb,hzbcap,hbalmargin,hxmargin,hwide⟩:=
      marked_joint_record_error_choice r c (κ/2) (thetaDeep/2) (η/2) (etaBal/2) (x/2) (tstar/2) Cparent Clocal cap
        (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hC hClocal hcap
  refine ⟨tolRef,ζActive,τP,tolP,ζP,τ,tol,ζLocal,row,ζrow,eb,zb,
    htol,htolcap,hζ,hζcap,?_,?_,?_,hτP,hτPcap,htolP,htolPcap,hζP,hζPcap,?_,?_,
    hτ,hτcap,htolLocal,htcap,?_,hζLocal,hζLocalCap,?_,hrow,hrowcap,hζrow,hζrowcap,?_,
    heb,hecap,hzb,hzbcap,hbalmargin,?_,?_⟩ <;> try linarith
  intro ε Cwide heps hwideC
  obtain ⟨ζWide,hz,hzcap,hw⟩:=hwide ε Cwide heps hwideC
  exact ⟨ζWide,hz,hzcap,by linarith⟩
end Oberwolfach
