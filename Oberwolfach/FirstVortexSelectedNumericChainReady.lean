module

public import Oberwolfach.FirstVortexCallerPreparedWithChain

@[expose] public section
/-! The fixed-terminal threshold is available uniformly at all later
ordinary matching tolerances selected within the prepared caps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexSelectedNumericChainReady
    (r d K:ℕ) (ρ₀ cap βfinal rho eta δLoss εInner δglobal:ℝ)
    (α ε cLocal chainCap active θ lamAssign lam ξCap δold δlocal bmatch ζret ηBalance κPack:ℝ):Prop :=
    ∀eps Δ ξPart:ℝ,0<eps→0≤Δ→Δ≤eps/8→0≤ξPart→ξPart≤ξCap→
      3*eps≤lam*(θ/(100*(K:ℝ)^2))→
      ∃hδ:0<δglobal,∃hθ:0<θ,∃hθδ:10*θ≤δglobal,∃hspacing:1/(d:ℝ)≤θ/1024,
      FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
        ε cLocal active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing ∧
      ∀ξPrep:ℝ,0≤ξPrep→4*ξPrep≤eps/2→∀e:ℕ,∃Nchain:ℕ,
      FirstVortexFixedTerminalChainAt α lam lamAssign ε δold δlocal δglobal θ eps ξPrep ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
        cap chainCap active ηBalance κPack βfinal Nchain
end Oberwolfach
