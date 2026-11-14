module

public import Oberwolfach.CompleteRemainderWithShield
public import Oberwolfach.AssignedEndpointExclusion
public import Oberwolfach.PrescribedSubtypeCompleteGlue

@[expose] public section
/-! Assign all bad edges from the actual lists and complete the prescribed
factor family while preserving the reserved and previously packed edges. -/
set_option autoImplicit false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V] [Nonempty I] [Nonempty V]
  {X Y:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)] [∀i,DecidableEq (Y i)]

theorem complete_remainder_and_glue_from_lists
    (pieces:∀i,List (PrescribedSourcePiece (X i)))
    (hshape:∀i p,p∈pieces i→p.Shape)
    (hapart:∀i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (A:∀i,Finset (X i)) (hA:∀i x,x∈A i→∀y,y∈A i→¬(prescribedDependentGraph pieces i).Adj x y)
    (f:∀i,X i→V) (hinj:∀i,Set.InjOn (f i) (↑(A i):Set (X i)))
    (embed:∀i,X i↪Y i) (Aold:∀i,Finset (Y i)) (ψ:∀i,Y i→V)
    (hOverlap:∀i x,x∈A i↔embed i x∈Aold i)
    (hψ:∀i,Set.InjOn (ψ i) (↑(Aold i):Set (Y i))) (hf:∀i x,x∈A i→f i x=ψ i (embed i x))
    (Kbad J:SimpleGraph V) (Lbad:Sym2 V→Finset I) (Bad:V→Finset I) (inner:Finset I) (Z:I→Finset V)
    (hOutside:∀e∈Kbad.edgeFinset,Disjoint (Lbad e) inner)
    (hOldZ:∀i,Disjoint ((Aold i).image (ψ i)) (Z i)) (houter:∀i,i∉inner→Z i=∅)
    (hOldShield:∀i e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈(Aold i).image (ψ i)→i∈Lbad e→i∈Bad v)
    (a b:ℝ) (ha:0<a) (hb:0≤b) (hbsmall:b≤a/16) (hnV:0<Fintype.card V)
    (hLbad:∀e∈Kbad.edgeFinset,a*Fintype.card V≤((Lbad e).card:ℝ))
    (hBad:∀v,((Bad v).card:ℝ)≤b*Fintype.card V)
    (hKbad:∀v,(Kbad.degree v:ℝ)≤b*Fintype.card V)
    (harc:∀i,Fintype.card (X i)≤(prescribedArcFinset (prescribedDependentDigraph pieces i)).card+(A i).card)
    (hcapacity:∀i,8*(A i).card+8*⌈4*(Kbad.edgeFinset.card:ℝ)/(a*Fintype.card V)⌉₊+4*(Z i).card+10≤Fintype.card (X i))
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hsize:∀i,(Fintype.card (X i):ℝ)≤δ*Fintype.card V)
    (hold:∀v,((Finset.univ.filter (fun i=>v∈(A i).image (f i))).card:ℝ)+Kbad.degree v+
      ((Finset.univ.filter (fun i=>v∈Z i)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀v,(J.degree v:ℝ)≤δ*Fintype.card V) (hKJ:Disjoint Kbad.edgeFinset J.edgeFinset)
    (D Dstar:V→V→Prop) (hDD:∀x y,D x y→Dstar x y)
    (hDstar:∀x y,Kbad.Adj x y→Dstar x y ∨ Dstar y x)
    (Pack:Finset (Sym2 V)) (hKPack:Disjoint Kbad.edgeFinset Pack) (hDPack:∀x y,D x y→s(x,y)∉Pack)
    (Lists:I→Finset V) (hext:∀i,IsExtendingList D (Lists i) β)
    (hListOld:∀i,Disjoint (Lists i) ((Aold i).image (ψ i))):
    ∃ (assign:Sym2 V→I) (orient:Sym2 V→V×V) (B:∀i,Finset (X i)) (g Φ:∀i,X i→V) (h:∀i,Y i→V),
      (∀i,Set.InjOn (h i) (↑(Aold i∪Finset.univ.image (embed i)):Set (Y i))) ∧
      (∀i y,y∈Aold i→h i y=ψ i y) ∧ (∀i x,h i (embed i x)=Φ i x) ∧
      (∀i,A i⊆B i ∧ (∀x∈A i,g i x=f i x) ∧
        (B i).image (g i)=(A i).image (f i)∪prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)∪Z i) ∧
      (∀i v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)→i∉Bad v) ∧
      (∀i v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)→
        ∃e∈Kbad.edgeFinset,v∈e.toFinset ∧ i∈Lbad e) ∧
      (∀i,Set.InjOn (Φ i) (↑(Finset.univ:Finset (X i)):Set (X i))) ∧
      (∀i x,x∈B i→Φ i x=g i x) ∧
      (∀i v,v∈Z i→∃x,Φ i x=v) ∧
      (∀i x,x∉B i→Φ i x∈Lists i) ∧
      (∀i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y) ∧
        ((x∉B i ∨ y∉B i)→D (Φ i x) (Φ i y))) ∧
      let E:I→Finset (Sym2 V):=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
      PairwisePhysicalDisjoint E ∧ Kbad.edgeFinset⊆Finset.univ.biUnion E ∧
      (∀i,Disjoint (E i) J.edgeFinset) ∧ (∀i,Disjoint (E i) Pack) ∧
      (∀v,(((Finset.univ.filter (fun z:(Σi,X i)=>z.2∉B z.1)).filter (fun z=>Φ z.1 z.2=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
      (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) := by
  have hAold:∀i,(A i).image (f i)⊆(Aold i).image (ψ i):=by
    intro i v hv
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨embed i x,(hOverlap i x).mp hx,?_⟩
    exact (hf i x hx).symm
  obtain ⟨assign,orient,B,g,Φ,hBg,hEnd,hEndList,hΦinj,hΦold,hZ,hL,hArc,hPair,hKcover,hJavoid,hPack,hFree,hUnion,hDegree⟩:=
    complete_remainder_with_image_and_shield pieces hshape hapart A hA f hinj Kbad J Lbad Bad inner Z
      (fun i=>(Aold i).image (ψ i)) hAold hOldShield hOutside hOldZ houter
      a b ha hb hbsmall hnV hLbad hBad hKbad harc hcapacity β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hKJ
      D Dstar hDD hDstar Pack hKPack hDPack Lists hext
  have hOldC:∀i,Disjoint ((Aold i).image (ψ i)) (prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)):=by
    intro i
    apply Finset.disjoint_left.mpr
    intro v hvOld hvC
    obtain ⟨e,he,hve,hi⟩:=hEndList i v hvC
    exact hEnd i v hvC (hOldShield i e v he hve hvOld hi)
  have hh:∀i,∃h:Y i→V,Set.InjOn h (↑(Aold i∪Finset.univ.image (embed i)):Set (Y i)) ∧
      (∀y∈Aold i,h y=ψ i y) ∧ (∀x,h (embed i x)=Φ i x):=by
    intro i
    have hΦ:Function.Injective (Φ i):=by
      intro x y he
      exact hΦinj i (Finset.mem_univ x) (Finset.mem_univ y) he
    exact prescribed_subtype_complete_factor_glue (embed i) (Aold i) (A i) (B i) (ψ i) (f i) (g i) (Φ i)
      (Lists i) (prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)) (Z i)
      (hOverlap i) (hBg i).1 (hψ i) hΦ (hf i) (hBg i).2.1 (hΦold i) (hBg i).2.2
      (hOldC i) (hOldZ i) (hL i) (hListOld i)
  choose h hinjH hOldH hRemH using hh
  exact ⟨assign,orient,B,g,Φ,h,hinjH,hOldH,hRemH,hBg,hEnd,hEndList,hΦinj,hΦold,hZ,hL,hArc,hPair,hKcover,hJavoid,hPack,hFree,hUnion,hDegree⟩
end Oberwolfach
