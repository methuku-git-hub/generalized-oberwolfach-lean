module

public import Oberwolfach.LongActualPhysicalGraphsInHost

@[expose] public section
/-! The selected surviving arcs together with the genuinely added physical
edges form an admissible directed host for residual placement. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selected_added_directed_host
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P Target Del:SimpleGraph V) (hTarget:Target≤P) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    let S₀:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let G:=Target\S₀
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
    let Dstar:=fun x y=>Dfree x y ∨ G.Adj x y;
    (∀x y,G.Adj x y→Dstar x y∨Dstar y x) ∧
    (∀x y,Dfree x y→Dstar x y) ∧
    (∀x y,Dstar x y→P.Adj x y) ∧
    (∀x y,Dfree x y→ rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y):=by
  intro S₀ G Dfree Dstar
  refine ⟨?_,?_,?_,?_⟩
  · intro x y h
    exact Or.inl (Or.inr h)
  · intro x y h
    exact Or.inl h
  · intro x y h
    rcases h with h|h
    · exact raw_selected_physical_relation_in_host P π d (fun e=>σ (Sum.inl e)) x y h.1
    · exact hTarget h.1
  · intro x y h
    exact h.1
end Oberwolfach
