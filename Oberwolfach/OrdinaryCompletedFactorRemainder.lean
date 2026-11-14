module

public import Oberwolfach.OrdinarySplitPhysicalRemainder
public import Oberwolfach.DirectedResidualEdgesInHost

@[expose] public section
/-! The remainder of the actual completed factor embeddings has the
reference agreement obtained from the same old and new physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_completed_factor_remainder
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {X:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (F:∀u,SimpleGraph (X u)) (f:∀u,X u→V) (Old New:U→Finset (Sym2 V))
    (Target Sample Reference Protect Bad:SimpleGraph V) (Inner:Finset V)
    (hRef:Reference≤Sample) (hProtect:Protect≤Reference) (hBad:Disjoint Reference Bad)
    (hInner:spanningRestriction Reference Inner≤Protect)
    (hTarget:∀v∈Inner,∀w∈Inner,Target.Adj v w↔Sample.Adj v w)
    (hAdj:∀u x y,(F u).Adj x y→(Target\Protect).Adj (f u x) (f u y))
    (hSplit:∀u,((F u).edgeFinset.image (Sym2.map (f u)))=Old u∪New u)
    (hCover:∀e∈(ordinaryPostmatchingRequired Target Sample Reference Bad (prescribedPhysicalUnion Old) Inner).edgeFinset,
      ∃u,e∈New u):
    let All:=fun u=>((F u).edgeFinset.image (Sym2.map (f u)))
    let Rem:=Target\prescribedPhysicalUnion All;
    Rem≤Sample ∧ Disjoint Rem Bad ∧
      (∀v∈Inner,∀w∈Inner,Rem.Adj v w↔Reference.Adj v w) :=by
  intro All Rem
  have hHost:∀u,All u⊆(Target\Protect).edgeFinset:=by
    intro u
    have hh:=directed_source_edge_images_subset_host (F u) (Target\Protect) (F u).Adj (f u)
      (by intro x y h;exact Or.inl h) (hAdj u)
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact ordinary_split_physical_remainder Old New All Target Sample Reference Protect Bad Inner
    hRef hProtect hBad hInner hTarget hSplit hHost hCover
end Oberwolfach
