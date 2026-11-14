module

public import Oberwolfach.ReservedPairMatchingHypotheses
public import Oberwolfach.ResidualActualLateContinuation
public import Oberwolfach.ProtectedListAbsorberShield

@[expose] public section
/-! Apply the actual residual continuation after deriving all label, old-shield,
and absorber-disjointness inputs from the same protected lists. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] [Nonempty I]
  {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_late_complement_with_reserved_pair_matching
    {n:ℕ} (F:∀i,SimpleGraph (X i)) (Dsrc:∀i,X i→X i→Prop)
    (hCont:LateComplementContinuation (V:=Fin n) F Dsrc)
    (K J:I→Type) [∀i,DecidableEq (K i)] [∀i,DecidableEq (J i)]
    (a:∀i,ActualResidualData (K:=K i) (J:=J i) (F i))
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) I Bool Bool)
    (aPair tPair:ℝ)
    (hpair:∀x y,x≠y→aPair-tPair≤(((Finset.univ:Finset I).filter (fun i=>
      rawIntervalFamilyState π d σ (x,i)=some (Sum.inr false) ∧
      rawIntervalFamilyState π d σ (y,i)=some (Sum.inr false))).card:ℝ)):
      ∃ pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}),
      (∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (X i))) ∧
      (∀i x y,prescribedDependentDigraph pieces i x y ↔ Dsrc i x.1 y.1 ∧ (a i).graph.Adj x.1 y.1) ∧
      ∀ (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
        (Interiors:∀i,Finset (X i)) (hDR:∀i,Disjoint (Interiors i) (a i).remaining)
        (ψ:∀i,X i→(Fin n)) (hψ:∀i,Set.InjOn (ψ i) (↑((a i).oldDomain\Interiors i):Set (X i))),
        ∀ (inner:Finset I),
        let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d σ) inner
        ∀(Abs:I→Finset (Fin n)),
        let Bad:(Fin n)→Finset I:=fun v=>Finset.univ.filter (fun i=>v∈Abs i)
        ∀ (Kbad Jbad:SimpleGraph (Fin n)) (Z:I→Finset (Fin n))
        (houter:∀i,i∉inner→Z i=∅)
        (hOldZ:∀i,Disjoint (((a i).oldDomain\Interiors i).image (ψ i)) (Z i))
        (hReservedOld:∀i,Disjoint (rawReservedSpokeList π d σ i) (((a i).oldDomain\Interiors i).image (ψ i)))
        (α b:ℝ) (hα:0<α) (hb:0≤b) (hbsmall:b≤α/16) (hnV:0<Fintype.card (Fin n))
        (hαmargin:α*n+inner.card≤aPair-tPair)
        (hAbsBudget:∀v,((Finset.univ.filter (fun i=>v∈Abs i)).card:ℝ)≤b*n)
        (hKbad:∀v,(Kbad.degree v:ℝ)≤b*Fintype.card (Fin n))
        (hcapacity:∀i,8*(residualSubtypeSet (a i).remaining (a i).prescribed).card+
          8*⌈4*(Kbad.edgeFinset.card:ℝ)/(α*Fintype.card (Fin n))⌉₊+4*(Z i).card+10≤Fintype.card {x // x∈(a i).remaining})
        (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
        (hnβ:100/β≤(Fintype.card (Fin n):ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card (Fin n):ℝ))
        (hI:(Fintype.card I:ℝ)≤Fintype.card (Fin n))
        (hsize:∀i,(Fintype.card {x // x∈(a i).remaining}:ℝ)≤δ*Fintype.card (Fin n))
        (hold:∀v,((Finset.univ.filter (fun i=>v∈
          (residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1))).card:ℝ)+Kbad.degree v+
          ((Finset.univ.filter (fun i=>v∈Z i)).card:ℝ)≤δ*Fintype.card (Fin n))
        (hJ:∀v,(Jbad.degree v:ℝ)≤δ*Fintype.card (Fin n)) (hKJ:Disjoint Kbad.edgeFinset Jbad.edgeFinset)
        (Dfree Dstar:(Fin n)→(Fin n)→Prop) (hDD:∀x y,Dfree x y→Dstar x y)
        (hDstar:∀x y,Kbad.Adj x y→Dstar x y ∨ Dstar y x)
        (Pack:Finset (Sym2 (Fin n))) (hKPack:Disjoint Kbad.edgeFinset Pack) (hDPack:∀x y,Dfree x y→s(x,y)∉Pack)
        (Lists:I→Finset (Fin n)) (hext:∀i,IsExtendingList Dfree (Lists i) β)
        (hListOld:∀i,Disjoint (Lists i) (((a i).oldDomain\Interiors i).image (ψ i)))
        (FinalEdges:∀i,Finset (Sym2 (X i)))
        (hOldPair:∀i j,i≠j→Disjoint (((a i).deletedEdges\FinalEdges i).image (Sym2.map (ψ i)))
          (((a j).deletedEdges\FinalEdges j).image (Sym2.map (ψ j))))
        (hOldPack:∀i,((a i).deletedEdges\FinalEdges i).image (Sym2.map (ψ i))⊆Pack),
      ∃ (assign:Sym2 (Fin n)→I) (orient:Sym2 (Fin n)→(Fin n)×(Fin n))
        (B:∀i,Finset {x // x∈(a i).remaining})
        (g Φ:∀i,{x // x∈(a i).remaining}→(Fin n)) (fC:∀i,{x // x∉Interiors i}↪(Fin n)),
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
        let E:I→Finset (Sym2 (Fin n)):=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
        PairwisePhysicalDisjoint E ∧ Kbad.edgeFinset⊆Finset.univ.biUnion E ∧
        (∀i,Disjoint (E i) Jbad.edgeFinset) ∧ (∀i,Disjoint (E i) Pack) ∧
        (∀i j,i≠j→Disjoint
          (((((F i).deleteEdges (↑(FinalEdges i):Set (Sym2 (X i)))).induce {x | x∉Interiors i}).edgeFinset).image (Sym2.map (fC i)))
          (((((F j).deleteEdges (↑(FinalEdges j):Set (Sym2 (X j)))).induce {x | x∉Interiors j}).edgeFinset).image (Sym2.map (fC j)))) ∧
        (∀v,(((Finset.univ.filter (fun z:(Σi,{x // x∈(a i).remaining})=>z.2∉B z.1)).filter
          (fun z=>Φ z.1 z.2=v)).card:ℝ)≤Real.sqrt δ*Fintype.card (Fin n)+1) ∧
        (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
        (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card (Fin n)) :=by
  obtain ⟨pieces,hgraph,harcs,hrest⟩:=hCont K J a
  refine ⟨pieces,hgraph,harcs,?_⟩
  intro hCycle Interiors hDR ψ hψ inner Lbad Abs Bad Kbad Jbad Z houter hOldZ hReservedOld α b hα hb hbsmall hnV hαmargin hAbsBudget hKbad hcapacity β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hKJ Dfree Dstar hDD hDstar Pack hKPack hDPack Lists hext hListOld FinalEdges hOldPair hOldPack
  let Old:=fun i=>((a i).oldDomain\Interiors i).image (ψ i)
  have hlabels:=reserved_pair_matching_hypotheses π d σ inner Old hReservedOld Kbad Bad α aPair tPair hαmargin hpair
  obtain ⟨hOutside,hShield,hLbad⟩:=hlabels
  have hBad:∀v:Fin n,((Bad v).card:ℝ)≤b*n:=hAbsBudget
  exact hrest hCycle Interiors hDR ψ hψ Kbad Jbad Lbad Bad inner Z (fun e _=>hOutside e) hOldZ houter hShield α b hα hb hbsmall hnV
    (by simpa only [Fintype.card_fin] using hLbad) (by simpa only [Fintype.card_fin] using hBad)
    hKbad hcapacity β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hKJ Dfree Dstar hDD hDstar Pack hKPack hDPack Lists hext hListOld FinalEdges hOldPair hOldPack
end Oberwolfach
