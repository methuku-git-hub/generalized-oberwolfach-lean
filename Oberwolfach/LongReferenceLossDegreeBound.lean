module

public import Oberwolfach.LongReferenceLossContainment
public import Oberwolfach.GraphDifferenceChangedDegree
public import Oberwolfach.CommonClassBalanceBounds
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! The loss of selected reference edges is controlled by the class-edit
budget and the newly completed physical-edge degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reference_loss_degree_bound
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n)))
    (hApprox:Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset)
    (ξ δ:ℝ)
    (hEdit:∀v,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)
    (hNew:∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤δ*n):
    let Sel:=longSelectedPhysicalGraph P π d σ
    let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E;
    ∀v,((Sel\(S\Small)).degree v:ℝ)≤(ξ+δ)*n:=by
  intro Sel Small v
  let State:=longPhysicalStateGraph P σ {0,1,2,3,4}
  let Edit:=State\S
  let New:=prescribedPhysicalUnion E
  have hsub:=long_reference_loss_containment P S π d σ Pack E hApprox
  have hle:((Sel\(S\Small)).degree v:ℝ)≤((Edit⊔New).degree v:ℝ):=by
    have hn:(Sel\(S\Small)).degree v≤(Edit⊔New).degree v:=by
      convert SimpleGraph.degree_le_of_le hsub using 1 <;> congr!
    exact_mod_cast hn
  have hsum:((Edit⊔New).degree v:ℝ)≤(Edit.degree v:ℝ)+New.degree v:=by
    have hn:(Edit⊔New).degree v≤Edit.degree v+New.degree v:=by
      convert graph_degree_sup_le Edit New v using 1 <;> congr!
    exact_mod_cast hn
  have hed:(Edit.degree v:ℝ)≤ξ*n:=by
    have he:=graph_difference_degree_le_changed State S v
    have he':(Edit.degree v:ℝ)≤(changed (S.neighborFinset v) (State.neighborFinset v)).card:=by exact_mod_cast he
    rw [changed_symm_eq] at he'
    exact he'.trans (hEdit v)
  have hnew:=hNew v
  nlinarith
end Oberwolfach
