module

public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The parent hubs outside the deeper vortex set, embedded in the original
hub domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

abbrev markedVortexNonDeeperHubType (i:ℕ):Type:=
  ↥((Finset.univ\markedVortexDeeperHubs Q i):Finset (markedVortexHubType Q i))

def markedVortexNonDeeperHubToPhysical (i:ℕ):markedVortexNonDeeperHubType Q i ↪ U where
  toFun u:=u.val.val
  inj':=by intro x y h;apply Subtype.ext;apply Subtype.ext;exact h
end Oberwolfach
