module

public import Oberwolfach.OrdinaryPostmatchingComplementAgreement
public import Oberwolfach.PrescribedFamilyPhysicalDegree

@[expose] public section
/-! An actual family of completed factor images splits into the old matching
edges and new forced edges. Its physical remainder has the required host
and reference agreement when the post-matching demand is covered. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_physical_union_split
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Old New All:U→Finset (Sym2 V)) (hSplit:∀u,All u=Old u∪New u):
    prescribedPhysicalUnion All=prescribedPhysicalUnion Old⊔prescribedPhysicalUnion New :=by
  ext x y
  change (SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion All):Set (Sym2 V))).Adj x y ↔
    (SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion Old):Set (Sym2 V))).Adj x y ∨
    (SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion New):Set (Sym2 V))).Adj x y
  simp only [SimpleGraph.fromEdgeSet_adj,Finset.mem_coe,Finset.mem_biUnion,Finset.mem_univ,true_and,hSplit,Finset.mem_union]
  aesop

theorem ordinary_physical_union_in_host
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Edges:U→Finset (Sym2 V)) (Host:SimpleGraph V) (hHost:∀u,Edges u⊆Host.edgeFinset):
    prescribedPhysicalUnion Edges≤Host :=by
  intro x y h
  have hh:=(SimpleGraph.fromEdgeSet_adj (↑(Finset.univ.biUnion Edges):Set (Sym2 V))).mp h
  obtain ⟨u,_,hu⟩:=Finset.mem_biUnion.mp hh.1
  exact SimpleGraph.mem_edgeFinset.mp (hHost u hu)

theorem ordinary_split_physical_remainder
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Old New All:U→Finset (Sym2 V)) (Target Sample Reference Protect Bad:SimpleGraph V) (Inner:Finset V)
    (hRef:Reference≤Sample) (hProtect:Protect≤Reference) (hBad:Disjoint Reference Bad)
    (hInner:spanningRestriction Reference Inner≤Protect)
    (hTarget:∀v∈Inner,∀w∈Inner,Target.Adj v w↔Sample.Adj v w)
    (hSplit:∀u,All u=Old u∪New u)
    (hHost:∀u,All u⊆(Target\Protect).edgeFinset)
    (hCover:∀e∈(ordinaryPostmatchingRequired Target Sample Reference Bad (prescribedPhysicalUnion Old) Inner).edgeFinset,
      ∃u,e∈New u):
    let Rem:=Target\prescribedPhysicalUnion All;
    Rem≤Sample ∧ Disjoint Rem Bad ∧
      (∀v∈Inner,∀w∈Inner,Rem.Adj v w↔Reference.Adj v w) :=by
  have hOld:∀u,Old u⊆(Target\Protect).edgeFinset:=by
    intro u e he
    apply hHost u
    rw [hSplit u]
    exact Finset.mem_union_left _ he
  have hNew:∀u,New u⊆(Target\Protect).edgeFinset:=by
    intro u e he
    apply hHost u
    rw [hSplit u]
    exact Finset.mem_union_right _ he
  have hcov:ordinaryPostmatchingRequired Target Sample Reference Bad (prescribedPhysicalUnion Old) Inner≤prescribedPhysicalUnion New:=by
    intro x y h
    have he:s(x,y)∈(ordinaryPostmatchingRequired Target Sample Reference Bad (prescribedPhysicalUnion Old) Inner).edgeFinset:=
      SimpleGraph.mem_edgeFinset.mpr h
    obtain ⟨u,hu⟩:=hCover s(x,y) he
    change (SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion New):Set (Sym2 V))).Adj x y
    exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,hu⟩,h.ne⟩
  have hh:=ordinary_postmatching_complement_agreement Target Sample Reference Protect Bad
    (prescribedPhysicalUnion Old) (prescribedPhysicalUnion New) Inner hRef hProtect hBad hInner hTarget
    (ordinary_physical_union_in_host Old (Target\Protect)
      (by intro u; convert hOld u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _))
    (ordinary_physical_union_in_host New (Target\Protect)
      (by intro u; convert hNew u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)) hcov
  rw [ordinary_physical_union_split Old New All hSplit]
  exact hh
end Oberwolfach
