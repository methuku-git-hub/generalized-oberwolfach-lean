module

public import Oberwolfach.LongRequiredPackingCoverage

@[expose] public section
/-! Covering the enlarged inner required graph also covers all close edges
needed by full-domain dual-type eligibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Fintype U]

theorem long_repaired_required_close_coverage
    (S Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (D:V→V→Prop)
    (Pack:Finset (Sym2 V)) (E:U→Finset (Sym2 V)):
    let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)
    let Old:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))
    let Kplus:=Kbase⊔spanningRestriction (Used\Old) I
    Kplus.edgeFinset⊆Finset.univ.biUnion E→
    longCloseRequiredGraph S π d D (fun x y=>Used.Adj x y)≤
      SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))⊔prescribedPhysicalUnion E:=by
  intro Kbase Old Kplus hcover
  have hbase:Kbase.edgeFinset⊆Finset.univ.biUnion E:=by
    intro e he
    apply hcover
    exact SimpleGraph.edgeFinset_mono (show Kbase≤Kplus from le_sup_left) he
  have hh:=long_required_graph_covered_by_prescribed_packing S (S\Used) Sel Used π d I D E hbase
  intro x y h
  exact Or.inr (hh h)
end Oberwolfach
