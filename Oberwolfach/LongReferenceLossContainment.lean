module

public import Oberwolfach.LongSelectedInnerClassPreservation
public import Oberwolfach.PhysicalSamplingLayerDisjoint
public import Oberwolfach.PrescribedFamilyPhysicalDegree

@[expose] public section
/-! Selected reference edges can be lost only through the class edit or the
newly completed edges; the old matching packing uses the approximate layer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reference_loss_containment
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P S:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Pack:Finset (Sym2 V)) (E:U→Finset (Sym2 V))
    (hApprox:Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset):
    let Sel:=longSelectedPhysicalGraph P π d σ
    let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))⊔prescribedPhysicalUnion E;
    Sel\(S\Small)≤(longPhysicalStateGraph P σ {0,1,2,3,4}\S)⊔prescribedPhysicalUnion E:=by
  intro Sel Small x y h
  have hs:Sel.Adj x y:=h.1
  have hnot:¬((S\Small).Adj x y):=h.2
  have hstate: (longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y:=
    long_selected_physical_subgraph_sampled_class P π d σ hs
  change ((longPhysicalStateGraph P σ {0,1,2,3,4}\S).Adj x y) ∨ (prescribedPhysicalUnion E).Adj x y
  by_cases hS:S.Adj x y
  · right
    have hsmall:Small.Adj x y:=by
      by_contra hsmall
      exact hnot ⟨hS,hsmall⟩
    change (SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))).Adj x y ∨ (prescribedPhysicalUnion E).Adj x y at hsmall
    rcases hsmall with hOld|hNew
    · have he:s(x,y)∈Pack:=((SimpleGraph.fromEdgeSet_adj _).mp hOld).1
      have ha:(longApproximatePhysicalGraph P π d σ).Adj x y:=SimpleGraph.mem_edgeFinset.mp (hApprox he)
      have hdis:=disjoint_iff_inf_le.mp (selected_and_approximate_rim_graphs_disjoint P π d σ)
      exact (hdis (show (Sel⊓longApproximatePhysicalGraph P π d σ).Adj x y from ⟨hs,ha⟩)).elim
    · exact hNew
  · exact Or.inl ⟨hstate,hS⟩
end Oberwolfach
