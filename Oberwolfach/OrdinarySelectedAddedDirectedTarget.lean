module

public import Oberwolfach.OrdinarySelectedAddedDirectedHost
public import Oberwolfach.OrdinarySampledSurvivalTarget

@[expose] public section
/-! Deleting only the sampled edges lost by the edited target makes both the
old approximate arcs and the selected/added residual host lie in the target. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selected_added_directed_target
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P Target Host Del:SimpleGraph V) (hTarget:Target≤P) (hHost:Host≤P)
    (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    let S₀:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let G:=Target\S₀
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
    let Dstar:=fun x y=>Dfree x y ∨ G.Adj x y;
    S₀\Target≤Del→
    (∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y→Target.Adj x y) ∧
    (∀x y,G.Adj x y→Dstar x y∨Dstar y x) ∧
    (∀x y,Dfree x y→Dstar x y) ∧
    (∀x y,Dstar x y→Target.Adj x y) ∧
    (∀x y,Dfree x y→ rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y):=by
  intro S₀ G Dfree Dstar hDel
  have hsurvive:=ordinary_sampled_survival_in_target P Target Host Del hHost π d σ hDel
  refine ⟨hsurvive.2,?_,?_,?_,?_⟩
  · intro x y h
    exact Or.inl (Or.inr h)
  · intro x y h
    exact Or.inl h
  · intro x y h
    rcases h with h|h
    · exact hsurvive.1 x y h.1 h.2
    · exact h.1
  · intro x y h
    exact h.1
end Oberwolfach
