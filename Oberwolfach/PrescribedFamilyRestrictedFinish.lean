module

public import Oberwolfach.PrescribedFamilyFinish
public import Oberwolfach.PrescribedSourceFamilyRestrictedInduction
public import Oberwolfach.PrescribedSourceFamilyInduction
public import Oberwolfach.PrescribedFamilyStateInitial

@[expose] public section
/-! Initialise the family induction and extract its prescribed images,
physical edge sets, directed arcs and actual free-image load. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_restricted_finish
    (QV:I→Finset X) (Q:I→SimpleGraph X) (A₀:I→Finset X) (ψ:I→X→V)
    (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hQsize:∀ i,((QV i).card:ℝ)≤δ*Fintype.card V) (hQdegree:∀ i x,(Q i).degree x≤2)
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
      (∀v,(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤κ*aScale+1) ∧
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
      (∀v,((((prescribedFreeSourceOccurrences QV A₀).filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤κ*aScale+1) := by
  let t:ℝ:=Real.sqrt δ*Fintype.card V
  have ht:0≤t:=by dsimp [t];positivity
  let st₀:PrescribedFamilyState I X V:=⟨A₀,ψ,∅,fun i=>prescribedInducedSourceEdges (Q i) (A₀ i),E₀,fun _=>∅⟩
  have hv₀:st₀.Valid QV Q A₀ ψ E₀ J t:=prescribed_induced_family_state_initial QV Q A₀ ψ E₀ J t ht hinj hA hE₀ hpair
  have hLocal₀:∀v,(((st₀.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st₀.vertexMap p=v)).card:ℝ)≤κ*aScale+1:=by
    intro v
    simp only [st₀,Finset.filter_empty,Finset.card_empty,Nat.cast_zero]
    positivity
  have hinit:∀ i,prescribedInducedSourceEdges (Q i) (A₀ i)⊆st₀.sourceEdges i:=by intro i;exact Finset.Subset.rfl
  have hfree:∀ p∈ps,∀ x∈p.2.vertices,x∉A₀ p.1→x∉st₀.assigned p.1:=by intro p hp x hx hnot;exact hnot
  obtain ⟨st,hv,hLocal,hmonoA,hmonoE,hpres,hL,harcs,hvertices,hedges⟩:=
    prescribed_source_family_restricted_induction QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
      hQsize hQdegree hold hJ Dsrc Fsrc hDQ D L hext H aScale κ θ haScale hκ hθ hH hθbudget hQlocal hδstrong hnstrong ps st₀ hv₀ hLocal₀ hinit hpieces hapart hfree hsubset
  have hassigned:∀ i,st.assigned i=QV i:=by
    intro i;apply Finset.Subset.antisymm (hv.2.2.1 i)
    intro x hx
    obtain ⟨p,hp,hpi,hpx⟩:=hcoverV i x hx
    have hh:=hvertices p hp (List.mem_toFinset.mpr hpx)
    simpa [hpi] using hh
  have hsource:∀ i,st.sourceEdges i=(Q i).edgeFinset:=by
    intro i;apply Finset.Subset.antisymm (hv.2.2.2.2.2.1 i)
    intro e he
    obtain ⟨p,hp,hpi,hpe⟩:=hcoverE i e he
    have hh:=hedges p hp hpe
    simpa [hpi] using hh
  have hfreeSubset:prescribedFreeSourceOccurrences QV A₀⊆st.freeOccurrences:=by
    intro p hp
    rcases p with ⟨i,x⟩
    change (i,x)∈Finset.univ.biUnion (fun j=>({j}:Finset I).product (QV j\A₀ j)) at hp
    obtain ⟨j,_,hprod⟩:=Finset.mem_biUnion.mp hp
    have hpair:=Finset.mem_product.mp hprod
    have hji:=Finset.mem_singleton.mp hpair.1
    have hmem:=Finset.mem_sdiff.mp hpair.2
    subst j
    obtain ⟨hx,hnot⟩:=hmem
    have hmember:x∈st.assigned i:=by rw [hassigned];exact hx
    rcases (hv.2.1 i x).mp hmember with hA'|hT
    · exact (hnot hA').elim
    · exact hT
  refine ⟨st,hv,hLocal,hassigned,hsource,?_,hv.2.2.2.1,?_,?_,?_,hv.2.2.2.2.2.2.2.2.1,?_,?_,?_⟩
  · intro i;simpa [hassigned i] using hv.1 i
  · intro i x hx hnot
    obtain ⟨p,hp,hpi,hpx⟩:=hcoverV i x hx
    have hh:=hL p hp x hpx (by simpa [hpi] using hnot)
    simpa [hpi] using hh
  · intro i x y hxy
    obtain ⟨p,hp,hpi,hpArc⟩:=hcoverA i x y hxy
    have hh:=harcs p hp (x,y) hpArc
    simp only [Prod.fst,Prod.snd] at hh
    rw [hpi] at hh
    rcases hh with hboth|hnew
    · constructor
      · rw [hv.2.2.2.1 i x hboth.1,hv.2.2.2.1 i y hboth.2]
        exact hpresArc i x y hxy hboth.1 hboth.2
      · intro hnot;rcases hnot with hnot|hnot
        · exact (hnot hboth.1).elim
        · exact (hnot hboth.2).elim
    · exact ⟨hDD _ _ hnew,fun _=>hnew⟩
  · intro i;rw [hv.2.2.2.2.2.2.2.1 i,hsource i]
  · intro i
    apply Finset.disjoint_left.mpr
    intro e he hj
    have hnot: e∉E₀ i:=(Finset.mem_sdiff.mp he).2
    have he':e∈st.physicalEdges i:=(Finset.mem_sdiff.mp he).1
    rw [hv.2.2.2.2.2.2.2.2.2.1 i] at he'
    rcases Finset.mem_union.mp he' with he'|he'
    · exact hnot he'
    · exact (Finset.disjoint_left.mp (hv.2.2.2.2.2.2.2.2.2.2 i) he') hj
  · intro v
    have hsub:((prescribedFreeSourceOccurrences QV A₀).filter (fun p=>familyVertexImage st.vertexMap p=v))⊆
        (st.freeOccurrences.filter (fun p=>familyVertexImage st.vertexMap p=v)):=by
      intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨hfreeSubset hp.1,hp.2⟩
    have hc:((((prescribedFreeSourceOccurrences QV A₀).filter (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤
        ((st.freeOccurrences.filter (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)):=by
      exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (hv.2.2.2.2.1 v)
  · intro v
    have hsub:((prescribedFreeSourceOccurrences QV A₀).filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st.vertexMap p=v)⊆
        (st.freeOccurrences.filter (fun p=>p.1∈H)).filter (fun p=>familyVertexImage st.vertexMap p=v):=by
      intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨⟨hfreeSubset hp.1.1,hp.1.2⟩,hp.2⟩
    have hc:((((prescribedFreeSourceOccurrences QV A₀).filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤
        (((st.freeOccurrences.filter (fun p=>p.1∈H)).filter (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ):=by
      exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (hLocal v)
end Oberwolfach
