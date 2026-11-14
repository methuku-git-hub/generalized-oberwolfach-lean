module

public import Oberwolfach.MarkedActiveRowParameterChoice
public import Oberwolfach.MarkedLargerHubLoadTolerance

@[expose] public section
/-! Compatible active row and load errors, with the larger-hub retention
error chosen after the vortex ratio. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_active_rows_loads_parameter_choice
    (η tstar τcap tolcap rowcap ζrowcap:ℝ)
    (hη:0<η) (ht:0<tstar) (hτcap:0<τcap) (htolcap:0<tolcap)
    (hrowcap:0<rowcap) (hζrowcap:0<ζrowcap):
    ∃ τ tol rowErr ζRow:ℝ,
      0<τ ∧ τ≤τcap ∧ 0<tol ∧ tol≤tolcap ∧ τ+tol≤η/8 ∧
      0<rowErr ∧ rowErr≤rowcap ∧ 0<ζRow ∧ ζRow≤ζrowcap ∧ rowErr+ζRow≤tstar/8 ∧
      ∀ ε capWide C:ℝ,0<ε→0<capWide→0≤C→
        ∃ ζWide:ℝ,0<ζWide ∧ ζWide≤capWide ∧ τ+tol+C*(4/ε)*ζWide≤η/4:=by
  let τ:=min τcap (η/64)
  let tol:=min tolcap (η/64)
  have hτ:0<τ:=by dsimp [τ];positivity
  have htol:0<tol:=by dsimp [tol];positivity
  have hτcap':τ≤τcap:=min_le_left _ _
  have htolcap':tol≤tolcap:=min_le_left _ _
  have hτbound:τ≤η/64:=min_le_right _ _
  have htolbound:tol≤η/64:=min_le_right _ _
  have hbase:τ+tol≤η/8:=by linarith
  obtain ⟨rowErr,ζRow,hrow,hrowcap',hζrow,hζrowcap',hrowbound⟩:=
    marked_active_row_parameter_choice 1 tstar rowcap ζrowcap ht hrowcap hζrowcap
  have hrowbound':rowErr+ζRow≤tstar/8:=by simpa only [Nat.cast_one,one_mul] using hrowbound
  refine ⟨τ,tol,rowErr,ζRow,hτ,hτcap',htol,htolcap',hbase,hrow,hrowcap',hζrow,hζrowcap',hrowbound',?_⟩
  intro ε capWide C he hcap hC
  exact marked_larger_hub_load_tolerance η capWide C (4/ε) τ tol hη hcap hC (by positivity) hbase
end Oberwolfach
