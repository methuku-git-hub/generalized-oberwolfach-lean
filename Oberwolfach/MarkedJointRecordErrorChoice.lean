module

public import Oberwolfach.MarkedParentNeighbourhoodParameterChoice
public import Oberwolfach.MarkedParentLoadParameterChoice
public import Oberwolfach.MarkedActiveRowsLoadsParameterChoice
public import Oberwolfach.MarkedBalanceRecordMargins

@[expose] public section
/-! Compatible numerical margins for the sampled parent and active record
inputs. The larger-hub retention error remains chosen after the vortex ratio. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_joint_record_error_choice
    (r c:ℕ) (κ thetaDeep η etaBal x tstar Cparent Clocal cap:ℝ)
    (hκ:0<κ) (hθ:0<thetaDeep) (hη:0<η) (hbal:0<etaBal) (hx:0<x)
    (ht:0<tstar) (hC:0≤Cparent) (hClocal:0≤Clocal) (hcap:0<cap):
    ∃ tolRef ζActive τParent tolParent ζParent τ tolLocal ζLocal rowErr ζRow epsBal ζBal:ℝ,
      0<tolRef ∧ tolRef≤cap ∧ 0<ζActive ∧ ζActive≤cap ∧
      tolRef+(r+12:ℕ)*ζActive≤κ/4 ∧ tolRef+(r+12:ℕ)*ζActive≤x/2 ∧ ζActive≤κ/4 ∧
      0<τParent ∧ τParent≤cap ∧ 0<tolParent ∧ tolParent≤cap ∧ 0<ζParent ∧ ζParent≤cap ∧
      τParent+tolParent+Cparent*ζParent≤κ/4 ∧ τParent+tolParent+Cparent*ζParent≤thetaDeep/4 ∧
      0<τ ∧ τ≤cap ∧ 0<tolLocal ∧ tolLocal≤cap ∧ τ+tolLocal≤η/8 ∧
      0<ζLocal ∧ ζLocal≤cap ∧ τ+tolLocal+Clocal*ζLocal≤η/4 ∧
      0<rowErr ∧ rowErr≤cap ∧ 0<ζRow ∧ ζRow≤cap ∧ rowErr+ζRow≤tstar/8 ∧
      0<epsBal ∧ epsBal≤cap ∧ 0<ζBal ∧ ζBal≤cap ∧
      epsBal+(c+2:ℕ)*ζBal≤etaBal ∧ epsBal+(c+2:ℕ)*ζBal≤x/2 ∧
      ∀ ε Cwide:ℝ,0<ε→0≤Cwide→∃ ζWide:ℝ,0<ζWide ∧ ζWide≤cap ∧
        τ+tolLocal+Cwide*(4/ε)*ζWide≤η/4:=by
  obtain ⟨tolRef,ζActive,htol,htolcap,hζ,hζcap,hκref,hxref,hζκ⟩:=
    marked_parent_neighbourhood_parameter_choice r κ x cap cap hκ hx hcap hcap
  obtain ⟨τP,tolP,ζP,hτP,hτPcap,htolP,htolPcap,hζP,hζPcap,hκP,hθP⟩:=
    marked_parent_load_parameter_choice κ thetaDeep Cparent cap cap cap hκ hθ hC hcap hcap hcap
  obtain ⟨τ,tol,row,ζrow,hτ,hτcap,htolLocal,htcap,hbase,hrow,hrowcap,hζrow,hζrowcap,hrowmargin,hwide⟩:=
    marked_active_rows_loads_parameter_choice η tstar cap cap cap cap hη ht hcap hcap hcap hcap
  obtain ⟨ζLocal,hζLocal,hζLocalCap,hlocal⟩:=hwide 4 cap Clocal (by norm_num) hcap hClocal
  have hlocal':τ+tol+Clocal*ζLocal≤η/4:=by norm_num at hlocal ⊢;exact hlocal
  obtain ⟨eb,zb,heb,hzb,hbalmargin,hxmargin⟩:=marked_balance_record_margin_choice c etaBal x hbal hx
  let e:=min eb cap
  let z:=min zb cap
  have he:0<e:=by dsimp [e];positivity
  have hz:0<z:=by dsimp [z];positivity
  have hecap:e≤cap:=min_le_right _ _
  have hzcap:z≤cap:=min_le_right _ _
  have hele:e≤eb:=min_le_left _ _
  have hzle:z≤zb:=min_le_left _ _
  have hc:(0:ℝ)≤(c+2:ℕ):=by positivity
  have hsum:e+(c+2:ℕ)*z≤eb+(c+2:ℕ)*zb:=by
    linarith [mul_le_mul_of_nonneg_left hzle hc]
  refine ⟨tolRef,ζActive,τP,tolP,ζP,τ,tol,ζLocal,row,ζrow,e,z,
    htol,htolcap,hζ,hζcap,hκref,hxref,hζκ,hτP,hτPcap,htolP,htolPcap,hζP,hζPcap,hκP,hθP,
    hτ,hτcap,htolLocal,htcap,hbase,hζLocal,hζLocalCap,hlocal',hrow,hrowcap,hζrow,hζrowcap,hrowmargin,he,hecap,hz,hzcap,
    hsum.trans hbalmargin,hsum.trans hxmargin,?_⟩
  intro ε Cwide heps hCwide
  exact hwide ε cap Cwide heps hcap hCwide
end Oberwolfach
