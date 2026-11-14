module

public import Oberwolfach.PrescribedSourceFamilyInduction
public import Oberwolfach.PrescribedSourcePieceRestrictedAdvance
public import Oberwolfach.PrescribedSourcePieces

@[expose] public section
/-! Iterate the actual path and cycle components of a family, preserving the
common load bound, all earlier images and each factor's directed arcs. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_source_family_restricted_induction
    (QV:I→Finset X) (Q:I→SimpleGraph X) (A₀:I→Finset X) (ψ:I→X→V)
    (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hQsize:∀ i,((QV i).card:ℝ)≤δ*Fintype.card V) (hQdegree:∀ i x,(Q i).degree x≤2)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (Dsrc:I→X→X→Prop) (Fsrc:I→SimpleGraph X) (hDQ:∀ i x y,Dsrc i x y→(Q i).Adj x y)
    (D:V→V→Prop) (L:I→Finset V) (hext:∀ i,IsExtendingList D (L i) β)
    (H:Finset I) (aScale κ θ:ℝ) (haScale:0<aScale) (hκ:0<κ) (hθ:0≤θ)
    (hH:(H.card:ℝ)≤aScale) (hθbudget:θ≤κ*(β/4))
    (hQlocal:∀i∈H,((QV i).card:ℝ)≤θ*Fintype.card V)
    (hδstrong:δ≤(β/200)^2) (hnstrong:200/β≤(Fintype.card V:ℝ))
    (ps:List (I×PrescribedSourcePiece X)) (st:PrescribedFamilyState I X V)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V))
    (hLocal:∀v,(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤κ*aScale+1)
    (hinit:∀ i,prescribedInducedSourceEdges (Q i) (A₀ i)⊆st.sourceEdges i)
    (hpieces:∀ p∈ps,p.2.Valid (Dsrc p.1) (Fsrc p.1))
    (hapart:ps.Pairwise PrescribedPiecesApart)
    (hfree:∀ p∈ps,∀ x∈p.2.vertices,x∉A₀ p.1→x∉st.assigned p.1)
    (hsubset:∀ p∈ps,∀ x∈p.2.vertices,x∈QV p.1):
    ∃ st':PrescribedFamilyState I X V,
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀v,(((st'.freeOccurrences.filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st'.vertexMap p=v)).card:ℝ)≤κ*aScale+1) ∧
      (∀ i,st.assigned i⊆st'.assigned i) ∧ (∀ i,st.sourceEdges i⊆st'.sourceEdges i) ∧
      (∀ i x,x∈st.assigned i→st'.vertexMap i x=st.vertexMap i x) ∧
      (∀ p∈ps,∀ x∈p.2.vertices,x∉A₀ p.1→st'.vertexMap p.1 x∈L p.1) ∧
      (∀ p∈ps,∀ e∈p.2.arcs,(e.1∈A₀ p.1 ∧ e.2∈A₀ p.1) ∨
        D (st'.vertexMap p.1 e.1) (st'.vertexMap p.1 e.2)) ∧
      (∀ p∈ps,p.2.vertices.toFinset⊆st'.assigned p.1) ∧
      (∀ p∈ps,p.2.edges⊆st'.sourceEdges p.1) := by
  induction ps generalizing st with
  | nil =>
    refine ⟨st,hvalid,hLocal,?_,?_,?_,?_,?_,?_,?_⟩
    · intro i;exact Finset.Subset.rfl
    · intro i;exact Finset.Subset.rfl
    · intro i x hx;rfl
    · simp
    · simp
    · simp
    · simp
  | cons p rest ih =>
    have hp:p.2.Valid (Dsrc p.1) (Fsrc p.1):=hpieces p (by simp)
    have hpieceRest:∀ q∈rest,q.2.Valid (Dsrc q.1) (Fsrc q.1):=by
      intro q hq;exact hpieces q (by simp [hq])
    have hpair:=List.pairwise_cons.mp hapart
    have hf:∀ x∈p.2.vertices,x∉A₀ p.1→x∉st.assigned p.1:=by
      intro x hx;exact hfree p (by simp) x hx
    have hs:∀ x∈p.2.vertices,x∈QV p.1:=by intro x hx;exact hsubset p (by simp) x hx
    obtain ⟨mid,hm,hmLocal,hmExact,hmA,hmE,hmPres,hmL,hmArcs,hmVertices,hmEdges⟩:=
      prescribed_source_piece_restricted_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
        hQsize hQdegree hold hJ p.1 (Dsrc p.1) (Fsrc p.1) (hDQ p.1) D (L p.1) (hext p.1)
        H aScale κ θ haScale hκ hθ hH hθbudget hQlocal hδstrong hnstrong p.2 hp st hvalid hLocal (hinit p.1) hf hs
    have hinitMid:∀ i,prescribedInducedSourceEdges (Q i) (A₀ i)⊆mid.sourceEdges i:=by
      intro i;exact (hinit i).trans (hmE i)
    have hfreeRest:∀ q∈rest,∀ x∈q.2.vertices,x∉A₀ q.1→x∉mid.assigned q.1:=by
      intro q hq x hx hnot hmem
      have hprev:=hfree q (by simp [hq]) x hx hnot
      have hpq:=hpair.1 q hq
      rw [hmExact] at hmem
      by_cases hi:q.1=p.1
      · rw [hi] at hprev hmem
        simp only [Function.update_self,Finset.mem_union] at hmem
        rcases hmem with hold'|hnew
        · exact hprev hold'
        · rcases hpq with hne|hdis
          · exact (hne hi.symm).elim
          · exact (Finset.disjoint_left.mp hdis hnew) (List.mem_toFinset.mpr hx)
      · simp only [Function.update_of_ne hi] at hmem
        exact hprev hmem
    have hsubRest:∀ q∈rest,∀ x∈q.2.vertices,x∈QV q.1:=by
      intro q hq x hx;exact hsubset q (by simp [hq]) x hx
    obtain ⟨last,hl,hlLocal,hlA,hlE,hlPres,hlL,hlArcs,hlVertices,hlEdges⟩:=
      ih mid hm hmLocal hinitMid hpieceRest hpair.2 hfreeRest hsubRest
    refine ⟨last,hl,hlLocal,?_,?_,?_,?_,?_,?_,?_⟩
    · intro i;exact (hmA i).trans (hlA i)
    · intro i;exact (hmE i).trans (hlE i)
    · intro i x hx;exact (hlPres i x (hmA i hx)).trans (hmPres i x hx)
    · intro q hq x hx hnot
      rcases List.mem_cons.mp hq with hq|hq
      · subst q
        rw [hlPres p.1 x (hmVertices (List.mem_toFinset.mpr hx))]
        exact hmL x hx hnot
      · exact hlL q hq x hx hnot
    · intro q hq e he
      rcases List.mem_cons.mp hq with hq|hq
      · subst q
        rcases hmArcs e he with hboth|hnew
        · exact Or.inl hboth
        · right
          have hend:=prescribed_source_piece_arc_endpoints p.2 e he
          rw [hlPres p.1 e.1 (hmVertices (List.mem_toFinset.mpr hend.1)),
              hlPres p.1 e.2 (hmVertices (List.mem_toFinset.mpr hend.2))]
          exact hnew
      · exact hlArcs q hq e he
    · intro q hq
      rcases List.mem_cons.mp hq with hq|hq
      · subst q;exact hmVertices.trans (hlA p.1)
      · exact hlVertices q hq
    · intro q hq
      rcases List.mem_cons.mp hq with hq|hq
      · subst q;exact hmEdges.trans (hlE p.1)
      · exact hlEdges q hq
end Oberwolfach
