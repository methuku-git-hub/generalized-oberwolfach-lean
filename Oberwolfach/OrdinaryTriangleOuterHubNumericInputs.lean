module

public import Oberwolfach.OrdinaryTriangleCommonRatesLateVortexError

@[expose] public section
/-! The outer triangle hub weights can be selected independently of the
inner hub constants, using the common preselected domain bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_outer_hub_numeric_inputs
    (cOuter COuter pstar Kdom:ℝ) (hc:0<cOuter) (hC:0<COuter) (hp:0<pstar):
    ∃b Bweight:ℝ,0<b ∧ b≤cOuter ∧ 0<Bweight ∧
      (4*COuter/pstar^(3*2+1))*Kdom^2≤Bweight :=by
  let b:ℝ:=cOuter/2
  let Bweight:ℝ:=(4*COuter/pstar^(3*2+1))*Kdom^2+1
  have hb:0<b:=by dsimp [b];positivity
  have hbase:0≤(4*COuter/pstar^(3*2+1))*Kdom^2:=by positivity
  have hB:0<Bweight:=by dsimp [Bweight];linarith
  exact ⟨b,Bweight,hb,by dsimp [b];linarith,hB,by dsimp [Bweight];linarith⟩
end Oberwolfach
