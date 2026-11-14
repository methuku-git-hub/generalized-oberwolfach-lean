module

public import Oberwolfach.PrescribedFamilyRestrictedFinish
public import Oberwolfach.PrescribedFamilyFinish
public import Oberwolfach.PrescribedFamilyPhysicalDegree
public import Oberwolfach.PrescribedSourceRepresentation

@[expose] public section
/-! Combine the complete component-list induction with the original load and
physical-union degree conclusions. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_restricted_embedding_from_components
    (QV:I→Finset X) (Q:I→SimpleGraph X) (A₀:I→Finset X) (ψ:I→X→V)
    (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hQsize:∀ i,((QV i).card:ℝ)≤δ*Fintype.card V)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (hinj:FamilyPartialInjections A₀ ψ) (hA:∀ i,A₀ i⊆QV i)
    (hE₀:∀ i,E₀ i=(prescribedInducedSourceEdges (Q i) (A₀ i)).image (Sym2.map (ψ i)))
    (hpair:PairwisePhysicalDisjoint E₀)
    (Dsrc:I→X→X→Prop) (Fsrc:I→SimpleGraph X) (hDQ:∀ i x y,Dsrc i x y→(Q i).Adj x y)
    (D Dstar:V→V→Prop) (hDD:∀ x y,D x y→Dstar x y)
    (hpresArc:∀ i x y,Dsrc i x y→x∈A₀ i→y∈A₀ i→Dstar (ψ i x) (ψ i y))
    (L:I→Finset V) (hext:∀ i,IsExtendingList D (L i) β)
    (H:Finset I) (aScale κ θ:ℝ) (haScale:0<aScale) (hκ:0<κ) (hθ:0≤θ)
    (hH:(H.card:ℝ)≤aScale) (hθbudget:θ≤κ*(β/4))
    (hQlocal:∀i∈H,((QV i).card:ℝ)≤θ*Fintype.card V)
    (hδstrong:δ≤(β/200)^2) (hnstrong:200/β≤(Fintype.card V:ℝ))
    (ps:List (I×PrescribedSourcePiece X))
    (hpieces:∀ p∈ps,p.2.Valid (Dsrc p.1) (Fsrc p.1))
    (hapart:ps.Pairwise PrescribedPiecesApart)
    (hsubset:∀ p∈ps,∀ x∈p.2.vertices,x∈QV p.1)
    (hcoverV:∀ i x,x∈QV i→∃ p∈ps,p.1=i ∧ x∈p.2.vertices)
    (hcoverE:∀ i e,e∈(Q i).edgeFinset→∃ p∈ps,p.1=i ∧ e∈p.2.edges)
    (hcoverA:∀ i x y,Dsrc i x y→∃ p∈ps,p.1=i ∧ (x,y)∈p.2.arcs):
    ∃ st:PrescribedFamilyState I X V,
      st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀ i,st.assigned i=QV i) ∧ (∀ i,st.sourceEdges i=(Q i).edgeFinset) ∧
      (∀ i,Set.InjOn (st.vertexMap i) (↑(QV i):Set X)) ∧
      (∀ i x,x∈A₀ i→st.vertexMap i x=ψ i x) ∧
      (∀ i x,x∈QV i→x∉A₀ i→st.vertexMap i x∈L i) ∧
      (∀ i x y,Dsrc i x y→Dstar (st.vertexMap i x) (st.vertexMap i y) ∧
        ((x∉A₀ i ∨ y∉A₀ i)→D (st.vertexMap i x) (st.vertexMap i y))) ∧
      (∀ i,st.physicalEdges i=((Q i).edgeFinset).image (Sym2.map (st.vertexMap i))) ∧
      PairwisePhysicalDisjoint st.physicalEdges ∧
      (∀ i,Disjoint (st.physicalEdges i\E₀ i) J.edgeFinset) ∧
      (∀ v,(((prescribedFreeSourceOccurrences QV A₀).filter
        (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
      (prescribedPhysicalUnion st.physicalEdges).edgeFinset=Finset.univ.biUnion st.physicalEdges ∧
      (∀ v,((prescribedPhysicalUnion st.physicalEdges).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) ∧
      (∀v,((((prescribedFreeSourceOccurrences QV A₀).filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤κ*aScale+1) := by
  have hQdegree:=prescribed_source_degree_from_components Q Dsrc Fsrc ps hpieces hapart hDQ hcoverE hcoverA
  obtain ⟨st,hv,hstateLocal,hassigned,hsource,hinj',hpres,hL,harcs,hE,hpair',hJ',hload,hrestricted⟩:=
    prescribed_family_restricted_finish QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
      hQsize hQdegree hold hJ hinj hA hE₀ hpair Dsrc Fsrc hDQ D Dstar hDD hpresArc L hext H aScale κ θ haScale hκ hθ hH hθbudget hQlocal hδstrong hnstrong ps
      hpieces hapart hsubset hcoverV hcoverE hcoverA
  have hdegree:=prescribed_family_physical_degree st QV Q A₀ ψ E₀ J β δ (Fintype.card V) hβ hβ1 hδ hδbound
    hn hQdegree hold hJ hv
  exact ⟨st,hv,hassigned,hsource,hinj',hpres,hL,harcs,hE,hpair',hJ',hload,hdegree.1,hdegree.2,hrestricted⟩
end Oberwolfach
