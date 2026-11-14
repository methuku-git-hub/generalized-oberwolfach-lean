module

public import Oberwolfach.ResidualActualLateContinuation
public import Oberwolfach.LongSelectedAlignedSourceWithLoad

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexResidualCompletionFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

def FirstVortexResidualCompletion
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (Dsrc:U→Fin n→Fin n→Prop)
    (K J:U→Type) [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (a:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (Interiors:U→Finset (Fin n)) (ψ:U→Fin n→Fin n)
    (Kbad Jbad:SimpleGraph (Fin n)) (Lbad:Sym2 (Fin n)→Finset U)
    (Bad:Fin n→Finset U) (Z:U→Finset (Fin n))
    (Dfree Dstar:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n)))
    (Lists:U→Finset (Fin n)) (FinalEdges:U→Finset (Sym2 (Fin n))) (δ:ℝ):Prop:=
    ∃pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}),
      (∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (Fin n))) ∧
      (∀i x y,prescribedDependentDigraph pieces i x y ↔ Dsrc i x.1 y.1 ∧ (a i).graph.Adj x.1 y.1) ∧
      ∃ (assign:Sym2 (Fin n)→U) (orient:Sym2 (Fin n)→(Fin n)×(Fin n))
        (B:∀i,Finset {x // x∈(a i).remaining})
        (g Φ:∀i,{x // x∈(a i).remaining}→Fin n) (fC:∀i,{x // x∉Interiors i}↪Fin n),
        (∀i (x:{x // x∉Interiors i}),x.val∈(a i).oldDomain→fC i x=ψ i x.val) ∧
        (∀i (x:{x // x∈(a i).remaining}) (hx:x.val∉Interiors i),fC i ⟨x.val,hx⟩=Φ i x) ∧
        (∀i,residualSubtypeSet (a i).remaining (a i).prescribed⊆B i ∧
          (∀x∈residualSubtypeSet (a i).remaining (a i).prescribed,g i x=ψ i x.1) ∧
          (B i).image (g i)=
            (residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1)∪
              prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)∪Z i) ∧
        (∀i v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)→i∉Bad v) ∧
        (∀i v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)→
          ∃e∈Kbad.edgeFinset,v∈e.toFinset ∧ i∈Lbad e) ∧
        (∀i x,x∈B i→Φ i x=g i x) ∧
        (∀i v,v∈Z i→∃x,Φ i x=v) ∧
        (∀i x,x∉B i→Φ i x∈Lists i) ∧
        (∀i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y) ∧
          ((x∉B i ∨ y∉B i)→Dfree (Φ i x) (Φ i y))) ∧
        let E:U→Finset (Sym2 (Fin n)):=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
        PairwisePhysicalDisjoint E ∧ Kbad.edgeFinset⊆Finset.univ.biUnion E ∧
        (∀i,Disjoint (E i) Jbad.edgeFinset) ∧ (∀i,Disjoint (E i) Pack) ∧
        (∀i j,i≠j→Disjoint
          (((((F i).deleteEdges (↑(FinalEdges i):Set (Sym2 (Fin n)))).induce {x | x∉Interiors i}).edgeFinset).image (Sym2.map (fC i)))
          (((((F j).deleteEdges (↑(FinalEdges j):Set (Sym2 (Fin n)))).induce {x | x∉Interiors j}).edgeFinset).image (Sym2.map (fC j)))) ∧
        (∀v,(((Finset.univ.filter (fun z:(Σi:U,{x // x∈(a i).remaining})=>z.2∉B z.1)).filter
          (fun z=>Φ z.1 z.2=v)).card:ℝ)≤Real.sqrt δ*Fintype.card (Fin n)+1) ∧
        (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
        (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card (Fin n))
end Oberwolfach
