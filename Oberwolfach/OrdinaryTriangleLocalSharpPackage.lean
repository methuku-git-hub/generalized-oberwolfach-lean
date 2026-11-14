module

public import Oberwolfach.OrdinaryTriangleLocalSharpInputs

@[expose] public section
/-! A local sharp package records the actual edit and parent rate used by a
host, retaining the common sample rather than postulating a certificate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleLocalSharpPackage
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U]
    (P G F:SimpleGraph V) (H:V→U→Prop) (I T:Finset V) (B W:Finset U)
    (π:Equiv.Perm V) (d k:ℕ) (hk:3≤3) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (α ω βout b Bweight hpack δpack εstar cLinear p τ eps bHub BHub ηhub:ℝ)
    (pR pH density tR tH βeParent βhParent ξroot aLoad ellCap cap βeGeo βhGeo lamInner ε:ℝ):Prop :=
    ∃Ledit rateParent:ℝ,0≤Ledit ∧ rateParent≤lamInner*ε/4 ∧
      OrdinaryTriangleLocalSharpInputs P G F H I T B W π d k hk s j raw
        α ω βout b Bweight hpack δpack εstar cLinear p τ eps bHub BHub ηhub
        pR pH density tR tH Ledit rateParent βeParent βhParent ξroot aLoad ellCap cap βeGeo βhGeo
end Oberwolfach
