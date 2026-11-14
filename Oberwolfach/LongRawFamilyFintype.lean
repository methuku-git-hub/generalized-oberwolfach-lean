module

public import Oberwolfach.LongRawMatchingRealizations

@[expose] public section
/-! The raw mixed family is finite for each of its component indices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

instance longRawSeedFamiliesFintype (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (ℓ:Fin K→ℕ) (i:Option (Fin K)):
    Fintype (longRawSeedFamilies (U:=U) π d m ℓ i):=by
  cases i with
  | none => dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
  | some i => dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
end Oberwolfach
