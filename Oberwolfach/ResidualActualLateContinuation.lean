module

public import Oberwolfach.ResidualActualLateIndicesComplementAligned

@[expose] public section
/-! The residual continuation may be retained after the cycle orders are
chosen, so later matching-dependent index types can be supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype V] [DecidableEq V] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

def LateComplementContinuation (F:∀i,SimpleGraph (X i)) (D:∀i,X i→X i→Prop):Prop :=
      ∀ (K J:I→Type) [∀i,DecidableEq (K i)] [∀i,DecidableEq (J i)],
      ∀ a:∀i,ActualResidualData (K:=K i) (J:=J i) (F i),
      ∃ pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}),
      (∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (X i))) ∧
      (∀i x y,prescribedDependentDigraph pieces i x y ↔ D i x.1 y.1 ∧ (a i).graph.Adj x.1 y.1) ∧
      ∀ (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
        (Interiors:∀i,Finset (X i)) (hDR:∀i,Disjoint (Interiors i) (a i).remaining)
        (ψ:∀i,X i→V) (hψ:∀i,Set.InjOn (ψ i) (↑((a i).oldDomain\Interiors i):Set (X i)))
        (Kbad Jbad:SimpleGraph V) (Lbad:Sym2 V→Finset I) (Bad:V→Finset I) (inner:Finset I) (Z:I→Finset V)
        (hOutside:∀e∈Kbad.edgeFinset,Disjoint (Lbad e) inner)
        (hOldZ:∀i,Disjoint (((a i).oldDomain\Interiors i).image (ψ i)) (Z i)) (houter:∀i,i∉inner→Z i=∅)
        (hOldShield:∀i e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈((a i).oldDomain\Interiors i).image (ψ i)→i∈Lbad e→i∈Bad v)
        (α b:ℝ) (hα:0<α) (hb:0≤b) (hbsmall:b≤α/16) (hnV:0<Fintype.card V)
        (hLbad:∀e∈Kbad.edgeFinset,α*Fintype.card V≤((Lbad e).card:ℝ))
        (hBad:∀v,((Bad v).card:ℝ)≤b*Fintype.card V)
        (hKbad:∀v,(Kbad.degree v:ℝ)≤b*Fintype.card V)
        (hcapacity:∀i,8*(residualSubtypeSet (a i).remaining (a i).prescribed).card+
          8*⌈4*(Kbad.edgeFinset.card:ℝ)/(α*Fintype.card V)⌉₊+4*(Z i).card+10≤Fintype.card {x // x∈(a i).remaining})
        (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
        (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
        (hI:(Fintype.card I:ℝ)≤Fintype.card V)
        (hsize:∀i,(Fintype.card {x // x∈(a i).remaining}:ℝ)≤δ*Fintype.card V)
        (hold:∀v,((Finset.univ.filter (fun i=>v∈
          (residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1))).card:ℝ)+Kbad.degree v+
          ((Finset.univ.filter (fun i=>v∈Z i)).card:ℝ)≤δ*Fintype.card V)
        (hJ:∀v,(Jbad.degree v:ℝ)≤δ*Fintype.card V) (hKJ:Disjoint Kbad.edgeFinset Jbad.edgeFinset)
        (Dfree Dstar:V→V→Prop) (hDD:∀x y,Dfree x y→Dstar x y)
        (hDstar:∀x y,Kbad.Adj x y→Dstar x y ∨ Dstar y x)
        (Pack:Finset (Sym2 V)) (hKPack:Disjoint Kbad.edgeFinset Pack) (hDPack:∀x y,Dfree x y→s(x,y)∉Pack)
        (Lists:I→Finset V) (hext:∀i,IsExtendingList Dfree (Lists i) β)
        (hListOld:∀i,Disjoint (Lists i) (((a i).oldDomain\Interiors i).image (ψ i)))
        (FinalEdges:∀i,Finset (Sym2 (X i)))
        (hOldPair:∀i j,i≠j→Disjoint (((a i).deletedEdges\FinalEdges i).image (Sym2.map (ψ i)))
          (((a j).deletedEdges\FinalEdges j).image (Sym2.map (ψ j))))
        (hOldPack:∀i,((a i).deletedEdges\FinalEdges i).image (Sym2.map (ψ i))⊆Pack),
      ∃ (assign:Sym2 V→I) (orient:Sym2 V→V×V)
        (B:∀i,Finset {x // x∈(a i).remaining})
        (g Φ:∀i,{x // x∈(a i).remaining}→V) (fC:∀i,{x // x∉Interiors i}↪V),
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
        let E:I→Finset (Sym2 V):=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
        PairwisePhysicalDisjoint E ∧ Kbad.edgeFinset⊆Finset.univ.biUnion E ∧
        (∀i,Disjoint (E i) Jbad.edgeFinset) ∧ (∀i,Disjoint (E i) Pack) ∧
        (∀i j,i≠j→Disjoint
          (((((F i).deleteEdges (↑(FinalEdges i):Set (Sym2 (X i)))).induce {x | x∉Interiors i}).edgeFinset).image (Sym2.map (fC i)))
          (((((F j).deleteEdges (↑(FinalEdges j):Set (Sym2 (X j)))).induce {x | x∉Interiors j}).edgeFinset).image (Sym2.map (fC j)))) ∧
        (∀v,(((Finset.univ.filter (fun z:(Σi,{x // x∈(a i).remaining})=>z.2∉B z.1)).filter
          (fun z=>Φ z.1 z.2=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
        (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
        (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V)
end Oberwolfach
