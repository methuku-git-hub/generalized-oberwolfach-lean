module

public import Oberwolfach.LongPreparationPhysicalContainment
public import Oberwolfach.PrescribedFamilyPhysicalDegree

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Fintype U]

theorem long_required_graph_covered_by_prescribed_packing
    (S P₀ Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (D:V→V→Prop)
    (E:U→Finset (Sym2 V))
    (hcover:(longRequiredPhysicalGraph S P₀ Sel π d I D (fun x y=>Used.Adj x y)).edgeFinset⊆Finset.univ.biUnion E):
    longCloseRequiredGraph S π d D (fun x y=>Used.Adj x y)≤prescribedPhysicalUnion E:=by
  intro x y h
  have hK:(longRequiredPhysicalGraph S P₀ Sel π d I D (fun x y=>Used.Adj x y)).Adj x y:=Or.inr h
  have he:s(x,y)∈(longRequiredPhysicalGraph S P₀ Sel π d I D (fun x y=>Used.Adj x y)).edgeFinset:=by
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hK
  have hmem:=hcover he
  apply (SimpleGraph.fromEdgeSet_adj _).mpr
  exact ⟨hmem,h.1.ne⟩
end Oberwolfach
