module

public import Oberwolfach.OrdinaryShiftedDeletedPhysicalState

@[expose] public section
/-! Physical rim deletion never activates a typed resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_deleted_state_mono
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (g:Γ) (j:Color) (F:Finset (Sym2 V)) (z:((V×V)⊕(V×V))⊕(Bool×V×U)):
    typedMarkedResourceState (ordinaryShiftedPairRims P π d (rawMarkedDeleteRims raw F))
      (rawMarkedPairSpokes π d (rawMarkedDeleteRims raw F) g j) z=true→
    typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j) z=true :=by
  intro h
  rw [ordinary_shifted_deleted_physical_state] at h
  cases hstate:typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j) z <;> simp [hstate] at h ⊢
end Oberwolfach
