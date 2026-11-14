module

public import Oberwolfach.OrdinaryRawPairRestriction
public import Oberwolfach.RawIntervalVertexRestriction

@[expose] public section
/-! Both sampled rims and interval spokes commute with fixed compatible
injections, including the whole permutation window. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem ordinaryRawRestrictPair_rim (f:W→V) (g:Z→U)
    (P:SimpleGraph V) (σ:RawWheelOutcome V U Γ Color) (x y:W):
    (rawWheelGraph (P.comap f) (ordinaryRawRestrictPair f g σ)).Adj x y ↔
      (rawWheelGraph P σ).Adj (f x) (f y):=by
  rfl

theorem ordinaryRawRestrictPair_spoke (f:W→V) (hf:Function.Injective f) (g:Z→U)
    (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hcomm:∀x,f (ρ x)=π (f x))
    (d:ℕ) (σ:RawWheelOutcome V U Γ Color) (j:Color) (x:W) (z:Z):
    rawWheelSpokes ρ d (ordinaryRawRestrictPair f g σ) j x z ↔
      rawWheelSpokes π d σ j (f x) (g z):=by
  have hσ:(fun e=>ordinaryRawRestrictPair f g σ (Sum.inr (z,e)))=
      rawIntervalRestrictVertices f (fun e=>σ (Sum.inr (g z,e))):=by
    funext e
    cases e with
    | inl e=>rfl
    | inr e=>cases e <;> rfl
  change rawIntervalState ρ d (fun e=>ordinaryRawRestrictPair f g σ (Sum.inr (z,e))) x=_ ↔ _
  rw [hσ,rawIntervalState_restrict f hf π ρ hcomm]
  rfl
end Oberwolfach
