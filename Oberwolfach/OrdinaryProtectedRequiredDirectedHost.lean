module

public import Oberwolfach.OrdinaryProtectedRequiredEdges
public import Oberwolfach.OrdinarySampledSurvivalTarget

@[expose] public section
/-! Required edges, surviving selected arcs and old approximate arcs all
lie in the edited target after removing the protected reservoir rim. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) ordinaryProtectedRequiredSix:DecidableEq (Fin 6):=instDecidableEqFin 6
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem ordinary_protected_required_directed_host
    (P Target Reference Protect Host:SimpleGraph V) (hHost:Host≤P) (Inner:Finset V)
    (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4};
    Reference≤Sample → Protect≤Reference →
    let G:=ordinaryProtectedRequired Target Sample Reference Inner
    let Del:=ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner
    let Base:=Target\Protect
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
    let Dstar:=fun x y=>Dfree x y ∨ G.Adj x y;
    (∀x y,G.Adj x y→Dstar x y∨Dstar y x) ∧
    (∀x y,Dfree x y→Dstar x y) ∧
    (∀x y,Dstar x y→Base.Adj x y) ∧
    (∀x y,Dfree x y→ rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y) ∧
    (∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y→Base.Adj x y):=by
  intro Sample hRef hProtect G Del Base Dfree Dstar
  have hrel:=ordinary_protected_required_edges_relations Target Sample Reference Protect Inner hRef hProtect
  have hDel:Sample\Base≤Del:=by
    intro x y he
    by_contra hn
    exact he.2 (hrel.2.1 ⟨he.1,hn⟩)
  have hsurvive:=ordinary_sampled_survival_in_target P Base Host Del hHost π d σ hDel
  refine ⟨?_,?_,?_,?_,hsurvive.2⟩
  · intro x y h;exact Or.inl (Or.inr h)
  · intro x y h;exact Or.inl h
  · intro x y h
    rcases h with h|h
    · exact hsurvive.1 x y h.1 h.2
    · exact hrel.1 h
  · intro x y h;exact h.1
end Oberwolfach
