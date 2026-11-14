module

public import Oberwolfach.FirstVortexSelectorSameSampleFactorSeedReadyDef

@[expose] public section
/-! The selector and factor caller use extensionally equal selected-state
sets, although their finite equality instances are elaborated differently. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_selector_selected_state_set_alignment :
    (letI:DecidableEq (Fin 6):=referenceWitnessFinDecidable 6; ({0,1,2,3,4}:Finset (Fin 6))) =
    (letI:DecidableEq (Fin 6):=instDecidableEqFin 6; ({0,1,2,3,4}:Finset (Fin 6))) :=by
  ext i
  simp

theorem first_vortex_selector_selected_state_graph_alignment
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e):
    (letI:DecidableEq (Fin 6):=referenceWitnessFinDecidable 6; longPhysicalStateGraph P σ {0,1,2,3,4}) =
    (letI:DecidableEq (Fin 6):=instDecidableEqFin 6; longPhysicalStateGraph P σ {0,1,2,3,4}) :=by
  exact congrArg (longPhysicalStateGraph P σ) first_vortex_selector_selected_state_set_alignment
end Oberwolfach
