module

public import Oberwolfach.MarkedReservedTerminalAbsorberProperty
public import Oberwolfach.MarkedSampleArcs

@[expose] public section

/-! The reserved-absorber property depends on the actual typed rim
relations, not on unused coordinates of the raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_reserved_property_physical_congruence
    (P:SimpleGraph V) (π:Equiv.Perm V) (b l s a₀ b₀ e₀ f:ℕ) (ε:ℝ)
    (σ τ:Sym2 V→Option (Bool×Bool)) (H₀ HK:V→U→Prop)
    (hR:∀ mark x y,markedPhysicalRim P π b σ mark x y=markedPhysicalRim P π b τ mark x y):
    MarkedReservedTerminalAbsorberProperty
      (fun e:MarkedSampleArc P π b σ false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π b σ true=>e.val.1) (fun e=>e.val.2)
      H₀ HK π b l s a₀ b₀ e₀ f ε →
    MarkedReservedTerminalAbsorberProperty
      (fun e:MarkedSampleArc P π b τ false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π b τ true=>e.val.1) (fun e=>e.val.2)
      H₀ HK π b l s a₀ b₀ e₀ f ε := by
  let R:=fun (P₀ P₁:V×V→Prop)=>MarkedReservedTerminalAbsorberProperty
    (fun e:{z:V×V // P₀ z}=>e.val.1) (fun e=>e.val.2)
    (fun e:{z:V×V // P₁ z}=>e.val.1) (fun e=>e.val.2)
    H₀ HK π b l s a₀ b₀ e₀ f ε
  have he (mark:Bool):
      (fun z:V×V=>markedPhysicalRim P π b σ mark z.1 z.2=1)=
      (fun z:V×V=>markedPhysicalRim P π b τ mark z.1 z.2=1):=by
    funext z;exact propext (by rw [hR mark z.1 z.2])
  change R (fun z=>markedPhysicalRim P π b σ false z.1 z.2=1)
    (fun z=>markedPhysicalRim P π b σ true z.1 z.2=1) →
    R (fun z=>markedPhysicalRim P π b τ false z.1 z.2=1)
    (fun z=>markedPhysicalRim P π b τ true z.1 z.2=1)
  intro h
  rw [he false,he true] at h
  exact h
end Oberwolfach
