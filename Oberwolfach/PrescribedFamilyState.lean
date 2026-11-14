module

public import Oberwolfach.PrescribedFamilyComponentInvariant
public import Oberwolfach.PrescribedFamilyDomains
public import Oberwolfach.PrescribedFamilySourceEdges

@[expose] public section
/-! A family state records the partial vertex maps, free occurrences and
corresponding source/physical edge sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure PrescribedFamilyState (I X V:Type) where
  assigned:I→Finset X
  vertexMap:I→X→V
  freeOccurrences:Finset (I×X)
  sourceEdges:I→Finset (Sym2 X)
  physicalEdges:I→Finset (Sym2 V)
  newEdges:I→Finset (Sym2 V)

variable {I X V:Type} [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

def PrescribedFamilyState.Valid (st:PrescribedFamilyState I X V)
    (QV:I→Finset X) (Q:I→SimpleGraph X) (A₀:I→Finset X) (ψ:I→X→V)
    (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V) (t:ℝ):Prop:=
  FamilyPartialInjections st.assigned st.vertexMap ∧
  (∀ i x,x∈st.assigned i ↔ x∈A₀ i ∨ (i,x)∈st.freeOccurrences) ∧
  (∀ i,st.assigned i⊆QV i) ∧
  (∀ i x,x∈A₀ i→st.vertexMap i x=ψ i x) ∧
  (∀ v,((st.freeOccurrences.filter (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤t+1) ∧
  (∀ i,st.sourceEdges i⊆(Q i).edgeFinset) ∧
  (∀ i e,e∈st.sourceEdges i→∀ x∈e.toFinset,x∈st.assigned i) ∧
  (∀ i,st.physicalEdges i=(st.sourceEdges i).image (Sym2.map (st.vertexMap i))) ∧
  PairwisePhysicalDisjoint st.physicalEdges ∧
  (∀ i,st.physicalEdges i=E₀ i∪st.newEdges i) ∧
  (∀ i,Disjoint (st.newEdges i) J.edgeFinset)

end Oberwolfach
