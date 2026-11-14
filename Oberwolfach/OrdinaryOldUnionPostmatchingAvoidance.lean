module

public import Oberwolfach.OrdinaryPostmatchingRequired
public import Oberwolfach.PrescribedFamilyPhysicalDegree

@[expose] public section
/-! The post-matching demands avoid every old edge by construction, and
the old union inherits the reference-layer avoidance of its factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_old_union_postmatching_avoidance
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Old:U→Finset (Sym2 V)) (Host Target Sample Reference Bad:SimpleGraph V) (Inner:Finset V)
    (hOld:∀u,Old u⊆Host.edgeFinset):
    ∀u,Disjoint (Old u)
      (ordinaryPostmatchingRequired Target Sample Reference Bad (prescribedPhysicalUnion Old) Inner).edgeFinset :=by
  intro u
  apply Finset.disjoint_left.mpr
  intro e he hG
  have heHost: e∈Host.edgeFinset:=hOld u he
  induction e using Sym2.ind with
  | _ x y=>
    have hxy:Host.Adj x y:=SimpleGraph.mem_edgeFinset.mp heHost
    have hUsed:(prescribedPhysicalUnion Old).Adj x y:=by
      change (SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion Old):Set (Sym2 V))).Adj x y
      exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,he⟩,hxy.ne⟩
    have hh: (ordinaryPostmatchingRequired Target Sample Reference Bad (prescribedPhysicalUnion Old) Inner).Adj x y:=
      SimpleGraph.mem_edgeFinset.mp hG
    exact hh.2 hUsed

theorem ordinary_old_union_avoids_reference
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Old:U→Finset (Sym2 V)) (Reference:SimpleGraph V)
    (hOld:∀u,Disjoint (Old u) Reference.edgeFinset):
    Disjoint (prescribedPhysicalUnion Old) Reference :=by
  apply disjoint_iff_inf_le.mpr
  intro x y hh
  have hu:(s(x,y):Sym2 V)∈Finset.univ.biUnion Old:=by
    have h:=(SimpleGraph.fromEdgeSet_adj (↑(Finset.univ.biUnion Old):Set (Sym2 V))).mp hh.1
    exact h.1
  obtain ⟨u,_,hu⟩:=Finset.mem_biUnion.mp hu
  exact Finset.disjoint_left.mp (hOld u) hu (SimpleGraph.mem_edgeFinset.mpr hh.2)
end Oberwolfach
