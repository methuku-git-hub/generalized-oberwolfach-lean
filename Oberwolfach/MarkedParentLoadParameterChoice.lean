module

public import Oberwolfach.MarkedParentLoadRecordInputs

@[expose] public section
/-! A fixed tolerance choice for the parent local and potential-root loads. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem marked_parent_load_parameter_choice
    (κ θ C τcap tolcap ζcap:ℝ) (hκ:0<κ) (hθ:0<θ) (hC:0≤C)
    (hτcap:0<τcap) (htolcap:0<tolcap) (hζcap:0<ζcap):
    ∃ τ tol ζ:ℝ,0<τ ∧ τ≤τcap ∧ 0<tol ∧ tol≤tolcap ∧ 0<ζ ∧ ζ≤ζcap ∧
      τ+tol+C*ζ≤κ/4 ∧ τ+tol+C*ζ≤θ/4:=by
  let b:=min κ θ
  have hb:0<b:=by dsimp [b];positivity
  have hbκ:b≤κ:=min_le_left _ _
  have hbθ:b≤θ:=min_le_right _ _
  let τ:=min τcap (b/32)
  let tol:=min tolcap (b/32)
  let ζ:=min ζcap (b/(32*(C+1)))
  have hτ:0<τ:=by dsimp [τ];positivity
  have htol:0<tol:=by dsimp [tol];positivity
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hτcap':τ≤τcap:=min_le_left _ _
  have htolcap':tol≤tolcap:=min_le_left _ _
  have hζcap':ζ≤ζcap:=min_le_left _ _
  have hτb:τ≤b/32:=min_le_right _ _
  have htolb:tol≤b/32:=min_le_right _ _
  have hζb:ζ≤b/(32*(C+1)):=min_le_right _ _
  have hden:0<32*(C+1):=by positivity
  have hζmul:ζ*(32*(C+1))≤b:=(le_div_iff₀ hden).mp hζb
  have hCζ:C*ζ≤b/32:=by nlinarith
  refine ⟨τ,tol,ζ,hτ,hτcap',htol,htolcap',hζ,hζcap',?_,?_⟩ <;> linarith
end Oberwolfach
