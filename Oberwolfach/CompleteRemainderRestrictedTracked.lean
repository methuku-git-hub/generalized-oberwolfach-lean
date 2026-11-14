module

public import Oberwolfach.PrescribedAssignedFamilyRestrictedEmbedding
public import Oberwolfach.AssignedEdgePreparation
public import Oberwolfach.AssignedEndpointExclusion
public import Oberwolfach.PrescribedAssignedFamilyEmbeddingWithDisjointTargets

@[expose] public section
/-! Assign all bad edges from the actual lists and complete the prescribed
factor family while preserving the reserved and previously packed edges. -/
set_option autoImplicit false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V] [Nonempty I] [Nonempty V]
  {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem complete_remainder_with_restricted_image_and_disjoint_targets_tracked
    (pieces:∀i,List (PrescribedSourcePiece (X i)))
    (hshape:∀i p,p∈pieces i→p.Shape)
    (hapart:∀i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (A:∀i,Finset (X i)) (hA:∀i x,x∈A i→∀y,y∈A i→¬(prescribedDependentGraph pieces i).Adj x y)
    (f:∀i,X i→V) (hinj:∀i,Set.InjOn (f i) (↑(A i):Set (X i)))
    (Kbad J:SimpleGraph V) (Lbad:Sym2 V→Finset I) (Bad:V→Finset I) (inner:Finset I) (Z:I→Finset V)
    (Old:I→Finset V) (hAold:∀i,(A i).image (f i)⊆Old i)
    (hOldShield:∀i e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈Old i→i∈Lbad e→i∈Bad v)
    (hOutside:∀e∈Kbad.edgeFinset,Disjoint (Lbad e) inner)
    (hOldZ:∀i,Disjoint (Old i) (Z i))
    (hZavoid:∀i e v,e∈Kbad.edgeFinset→v∈e.toFinset→i∈Lbad e→v∉Z i)
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
    (H:Finset I) (aScale κ θ:ℝ) (haScale:0<aScale) (hκ:0<κ) (hθ:0≤θ)
    (hH:(H.card:ℝ)≤aScale) (hθbudget:θ≤κ*(β/4))
    (hQlocal:∀i∈H,(Fintype.card (X i):ℝ)≤θ*Fintype.card V)
    (hδstrong:δ≤(β/200)^2) (hnstrong:200/β≤(Fintype.card V:ℝ)):
    ∃ (assign:Sym2 V→I) (orient:Sym2 V→V×V) (B:∀i,Finset (X i)) (g Φ:∀i,X i→V),
      (∀e∈Kbad.edgeFinset,prescribedArcPhysical (orient e)=e) ∧
      (∀i,(prescribedAssignedArcs Kbad assign orient i).card≤⌈4*(Kbad.edgeFinset.card:ℝ)/(a*Fintype.card V)⌉₊) ∧
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
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) ∧
      (∀v,((((Finset.univ.filter (fun z:(Σi,X i)=>z.2∉B z.1)).filter (fun z=>z.1∈H)).filter
        (fun z=>Φ z.1 z.2=v)).card:ℝ)≤κ*aScale+1) := by
  obtain ⟨assign,orient,horient,hallowed,hmatching,hload,hOldM,hinner,hM,hMcap⟩:=
    prepare_assigned_bad_edges Kbad Dstar hDstar Lbad Bad (fun _=>∅) inner (by simp) hOutside
      a b ha hb hbsmall hnV hLbad hBad hKbad
  have hEnd:=assigned_endpoints_avoid_forbidden Kbad assign orient (fun e he=>(horient e he).1) Bad
    (fun e he v hv=>(hallowed e he).2 v hv)
  have hEndList:=assigned_endpoints_have_allowed_edge Kbad assign orient (fun e he=>(horient e he).1) Lbad
    (fun e he=>(hallowed e he).1)
  have hMZ:∀i,Disjoint (prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)) (Z i):=by
    intro i
    apply Finset.disjoint_left.mpr
    intro v hv hz
    obtain ⟨e,he,hve,hi⟩:=hEndList i v hv
    exact hZavoid i e v he hve hi hz
  have hOldM':∀i,Disjoint (Old i) (prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)):=by
    intro i
    apply Finset.disjoint_left.mpr
    intro v hvOld hvEnd
    obtain ⟨e,he,hve,hi⟩:=hEndList i v hvEnd
    exact hEnd i v hvEnd (hOldShield i e v he hve hvOld hi)
  have hOldM'':∀i,Disjoint ((A i).image (f i)) (prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)):=
    fun i=>(hOldM' i).mono (hAold i) (Finset.Subset.refl _)
  have hOldZ':∀i,Disjoint ((A i).image (f i)) (Z i):=
    fun i=>(hOldZ i).mono (hAold i) (Finset.Subset.refl _)
  have hcapacity':∀i,8*(A i).card+8*(prescribedAssignedArcs Kbad assign orient i).card+4*(Z i).card+10≤Fintype.card (X i):=by
    intro i
    have hh:=hcapacity i
    have hc:=hMcap i
    omega
  obtain ⟨B,g,Φ,hBg,hΦinj,hΦold,hZ,hL,hArc,hPair,hKcover,hJavoid,hPack,hFree,hUnion,hDegree,hRestricted⟩:=
    prescribed_assigned_family_restricted_embedding_with_image_disjoint_targets pieces hshape hapart A hA f hinj Kbad J assign orient
      (fun e he=>(horient e he).1) hmatching Z hMZ hOldM'' hOldZ' harc hcapacity'
      β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hKJ D Dstar hDD
      (fun e he=>(horient e he).2) Pack hKPack hDPack Lists hext H aScale κ θ haScale hκ hθ hH hθbudget hQlocal hδstrong hnstrong
  refine ⟨assign,orient,B,g,Φ,(fun e he=>(horient e he).1),hMcap,?_,hEnd,hEndList,hΦinj,hΦold,hZ,hL,hArc,hPair,hKcover,hJavoid,hPack,hFree,hUnion,hDegree,hRestricted⟩
  intro i
  exact ⟨(hBg i).1,(hBg i).2.1,(hBg i).2.2.1⟩
end Oberwolfach
