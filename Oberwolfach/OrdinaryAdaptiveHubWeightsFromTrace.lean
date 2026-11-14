module

public import Oberwolfach.OrdinaryAdaptiveHubWeightsLevelEvent
public import Oberwolfach.OrdinaryProtectedTraceHostLe

@[expose] public section
/-! The universal hub-weight event applies to the realized trace on the very
same sample once its profile has been verified. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' Γ Color:Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [Fintype Γ] [Fintype Color] [LinearOrder V'] [DecidableEq V] [DecidableEq U] [DecidableEq U']

theorem ordinary_adaptive_hub_weights_from_protected_trace
    (P Q G:SimpleGraph V) (H Hs:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (n:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost n A)
    (hstate:ordinaryHostResources G Hs=A) (hQP:Q≤P)
    (f:V'↪V) (g:U'↪U) (F:SimpleGraph V') (I:Finset V') (B:Finset U')
    (π:Equiv.Perm V') (d m:ℕ) (pR pH density tR tH L βe βh b Bweight η:ℝ)
    (s:U'→Color→ℝ) (j:Color) (σ:RawWheelOutcome V' U' Γ Color)
    (hevent:OrdinaryAdaptiveHubWeightsLevelEvent m (P.comap f) F I B π d pR pH density tR tH L βe βh b Bweight η s j σ)
    (hprofile:OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) F (fun v u=>Hs (f v) (g u))
      π d I B pR pH density tR tH L βe βh s j σ):
    Nonempty (OrdinaryMixedHubWeightsOfLength m b Bweight η (G.comap f) F (fun v u=>Hs (f v) (g u)) I B):=by
  have hGP:G≤P:=(ordinary_protected_trace_host_le Q G H Hs X T Z W cost deepCost n A htrace hstate).trans hQP
  have hlocal:(G.comap f)≤(P.comap f):=by intro v w hvw;exact hGP hvw
  exact hevent _ _ hprofile hlocal
end Oberwolfach
