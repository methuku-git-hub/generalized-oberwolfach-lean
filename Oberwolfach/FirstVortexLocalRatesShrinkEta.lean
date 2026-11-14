module

public import Oberwolfach.FirstVortexOrderedGeometryHierarchy

@[expose] public section
/-! Shrink the outside-change rate independently of the global matching
error while retaining the local and global rate margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_local_rates_shrink_eta
    (cap rho t etaOld etaNew δsmall δspoke sOld sNew:ℝ)
    (hrho:0<rho) (heta:0<etaNew) (hetale:etaNew≤etaOld)
    (hs:0≤sNew) (hsOld:sNew≤sOld) (hsEta:100*sNew≤etaNew)
    (hOld:∀ζret ηBalance θ a γ ξPart κ Δ b:ℝ,
      ζret≤sOld→ηBalance≤sOld→θ≤sOld→a≤sOld→γ≤sOld→ξPart≤sOld→κ≤sOld→Δ≤sOld→b≤sOld→
      FirstVortexLocalGeometryRateBounds cap rho t etaOld δsmall δspoke ζret ηBalance θ a γ ξPart κ Δ b):
    ∀ζret ηBalance θ a γ ξPart κ Δ b:ℝ,
      ζret≤sNew→ηBalance≤sNew→θ≤sNew→a≤sNew→γ≤sNew→ξPart≤sNew→κ≤sNew→Δ≤sNew→b≤sNew→
      FirstVortexLocalGeometryRateBounds cap rho t etaNew δsmall δspoke ζret ηBalance θ a γ ξPart κ Δ b :=by
  intro ζret ηBalance θ a γ ξPart κ Δ b hζ hbal hθ ha hγ hξ hκ hΔ hb
  obtain ⟨hS,hA,hB,hE,_,hret,hbalance,hrow,hcol⟩:=hOld ζret ηBalance θ a γ ξPart κ Δ b
    (hζ.trans hsOld) (hbal.trans hsOld) (hθ.trans hsOld) (ha.trans hsOld) (hγ.trans hsOld)
    (hξ.trans hsOld) (hκ.trans hsOld) (hΔ.trans hsOld) (hb.trans hsOld)
  have hmax:max a γ≤sNew:=max_le ha hγ
  have hLocal:Δ+2*(b+2*max a γ+κ)<etaNew:=by nlinarith
  have hcoeff:0≤1+2/rho:=by positivity
  have hmul:=mul_le_mul_of_nonneg_left hetale hcoeff
  refine ⟨hS,hA,hB,hE,hLocal,hret,hbalance,?_,hcol⟩
  nlinarith
end Oberwolfach
