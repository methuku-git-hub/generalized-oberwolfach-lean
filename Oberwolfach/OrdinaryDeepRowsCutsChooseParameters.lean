module

public import Oberwolfach.OrdinaryDeepRowsCutsAfterParameters

@[expose] public section
/-! Select all-level error parameters while preserving the later spacing and
vortex quantifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_rows_cuts_choose_parameters
    (m K:ℕ) (α ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (hdeep:OrdinaryDeepRowsCutsAfterEarly m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep)
    (aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut:ℝ)
    (haLoad:0<aLoad) (haLoadA:aLoad≤a) (hε:0<ε) (hε1:ε<1/4) (hεa:ε≤a) (hερ:ε≤ρ₀/16)
    (hξ:0<ξ) (hχinner:0<χinner) (hχdeep:0<χdeep) (hK:2/ε≤Kdom)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (hb:b≤c)
    (hB:(4*C/pmin^(3*m+1))*Kdom^m≤Bweight) (he:0<eParent) (hh:0<hParent)
    (hεR:0<εR) (hεH:0<εH) (hχone:0<χone) (hχtwo:0<χtwo) (hχcut:0<χcut):
    ∃t eEvent hEvent cap:ℝ,0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧
      eEvent≤eParent ∧ hEvent≤hParent ∧ OrdinaryDeepRowsCutsAfterParameters m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap :=by
  exact hdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut
    haLoad haLoadA hε hε1 hεa hερ hξ hχinner hχdeep hK hKdom hb hB he hh hεR hεH hχone hχtwo hχcut
end Oberwolfach
