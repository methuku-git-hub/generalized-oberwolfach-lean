module

public import Oberwolfach.MarkedFixedTerminalAbsorberOriginal

@[expose] public section
/-! The fixed terminal absorber on one explicitly named retained sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def LongNamedFixedAbsorber {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (σ:RawMarkedOutcome (Fin n) U Bool Bool) (H:Bool→Fin n→U→Prop)
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U):Prop:=
  MarkedFixedTerminalAbsorber P π d (r+4) σ H C X Z
end Oberwolfach
