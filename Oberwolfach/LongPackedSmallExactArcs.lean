module

public import Oberwolfach.LongPackedArcPhysicalUnion
public import Oberwolfach.PrescribedFamilyPhysicalDegree

@[expose] public section
/-! A loop-free old packing and the actual prescribed family form exactly the
physical edges of the family of canonical arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_packed_small_exact_arcs
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U]
    (Used:SimpleGraph V) (Pack:Finset (Sym2 V)) (E old:U→Finset (Sym2 V))
    (arcs:U→Finset (V×V)) (hPack:Pack⊆Used.edgeFinset)
    (hOld:Pack=Finset.univ.biUnion old)
    (hUnion:(prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E)
    (h:∀u,(arcs u).image (fun a=>s(a.1,a.2))=old u∪E u):
    (SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))⊔prescribedPhysicalUnion E).edgeFinset=
      (Finset.univ.biUnion arcs).image (fun a=>s(a.1,a.2)):=by
  have hp:(SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))).edgeFinset=Pack:=by
    apply Finset.Subset.antisymm
    · intro e he
      exact ((SimpleGraph.edgeSet_fromEdgeSet _).le (SimpleGraph.mem_edgeFinset.mp he)).1
    · intro e he
      induction e using Sym2.ind with
      | _ x y =>
        have hu:Used.Adj x y:=SimpleGraph.mem_edgeFinset.mp (hPack he)
        exact SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨he,hu.ne⟩)
  rw [SimpleGraph.edgeFinset_sup,hp,hUnion,hOld]
  exact (long_packed_arc_physical_union arcs old E h).symm
end Oberwolfach
