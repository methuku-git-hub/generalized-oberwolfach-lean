module

public import Oberwolfach.OrdinaryRawPairRestrictionGeometry

@[expose] public section
/-! The actual local sampled graph and spokes are the restrictions of the
same ambient raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem ordinary_raw_pair_graph_eq (f:W↪V) (g:Z↪U) (P:SimpleGraph V)
    (σ:RawWheelOutcome V U Γ Color):
    rawWheelGraph (P.comap f) (ordinaryRawRestrictPair f g σ)=(rawWheelGraph P σ).comap f:=by
  ext x y
  exact ordinaryRawRestrictPair_rim f g P σ x y

theorem ordinary_raw_pair_spokes_eq (f:W↪V) (g:Z↪U)
    (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hcomm:∀x,f (ρ x)=π (f x))
    (d:ℕ) (σ:RawWheelOutcome V U Γ Color) (j:Color):
    rawWheelSpokes ρ d (ordinaryRawRestrictPair f g σ) j=fun x z=>rawWheelSpokes π d σ j (f x) (g z):=by
  funext x z
  exact propext (ordinaryRawRestrictPair_spoke f f.injective g π ρ hcomm d σ j x z)
end Oberwolfach
