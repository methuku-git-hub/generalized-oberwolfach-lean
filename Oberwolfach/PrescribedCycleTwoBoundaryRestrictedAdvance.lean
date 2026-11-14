module

public import Oberwolfach.PrescribedOrderedPathFamilyRestrictedAdvance
public import Oberwolfach.PrescribedOrderedPathFamilyAdvance
public import Oberwolfach.PrescribedCycleTwoBoundarySplit

@[expose] public section
/-! Process a source cycle with two prescribed vertices by splitting it into
two ordered paths with distinct prescribed boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_cycle_two_boundary_restricted_advance
    (QV:I→Finset X) (Q:I→SimpleGraph X) (A₀:I→Finset X) (ψ:I→X→V)
    (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hQsize:∀ i,((QV i).card:ℝ)≤δ*Fintype.card V) (hQdegree:∀ i x,(Q i).degree x≤2)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (k:I) (Dsrc:X→X→Prop) (Fsrc:SimpleGraph X) (hDQ:∀ x y,Dsrc x y→(Q k).Adj x y)
    (D:V→V→Prop) (L:Finset V) (hext:IsExtendingList D L β)
    (H:Finset I) (aScale κ θ:ℝ) (haScale:0<aScale) (hκ:0<κ) (hθ:0≤θ)
    (hH:(H.card:ℝ)≤aScale) (hθbudget:θ≤κ*(β/4))
    (hQlocal:∀i∈H,((QV i).card:ℝ)≤θ*Fintype.card V)
    (hδstrong:δ≤(β/200)^2) (hnstrong:200/β≤(Fintype.card V:ℝ))
    (a b:X) (xs:List X) (hnodup:(a::xs).Nodup) (ha:a∈A₀ k) (hb:b∈A₀ k) (hbin:b∈xs)
    (hsourcecycle:DirectedCycleThrough Dsrc Fsrc (a::xs))
    (st:PrescribedFamilyState I X V)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V))
    (hLocal:∀v,(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤κ*aScale+1)
    (hinit:prescribedInducedSourceEdges (Q k) (A₀ k)⊆st.sourceEdges k)
    (hfree:∀ x∈a::xs,x∉A₀ k→x∉st.assigned k) (hsubset:∀ x∈a::xs,x∈QV k):
    ∃ st':PrescribedFamilyState I X V,
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀v,(((st'.freeOccurrences.filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st'.vertexMap p=v)).card:ℝ)≤κ*aScale+1) ∧
      st'.assigned=Function.update st.assigned k (st.assigned k∪(a::xs).toFinset) ∧
      (∀ i,st.assigned i⊆st'.assigned i) ∧ (∀ i,st.sourceEdges i⊆st'.sourceEdges i) ∧
      (∀ i x,x∈st.assigned i→st'.vertexMap i x=st.vertexMap i x) ∧
      (∀ x∈a::xs,x∉A₀ k→st'.vertexMap k x∈L) ∧
      (∀ e∈prescribedDirectedPathEdges ((a::xs)++[a]),
        (e.1∈A₀ k ∧ e.2∈A₀ k) ∨ D (st'.vertexMap k e.1) (st'.vertexMap k e.2)) ∧
      (a::xs).toFinset⊆st'.assigned k ∧
      prescribedOrderedPathEdges ((a::xs)++[a])⊆st'.sourceEdges k := by
  obtain ⟨pre,post,hxs,hp1,hp2,hinter,hphysical,hdirected⟩:=
    prescribed_cycle_two_boundary_split a b xs (List.nodup_cons.mp hnodup).1 (List.nodup_cons.mp hnodup).2 hbin
  let p1:List X:=a::pre++[b]
  let p2:List X:=b::post++[a]
  have hmem1:∀ x∈p1,x∈a::xs:=by
    intro x hx;simp [p1,hxs] at hx ⊢;tauto
  have hmem2:∀ x∈p2,x∈a::xs:=by
    intro x hx;simp [p2,hxs] at hx ⊢;tauto
  have hcover:∀ x∈a::xs,x∈p1 ∨ x∈p2:=by
    intro x hx;simp [p1,p2,hxs] at hx ⊢;tauto
  have hc:List.IsChain (fun x y=>Dsrc x y ∧ ¬Fsrc.Adj x y) ((a::xs)++[a]):=by
    exact (prescribed_path_through_chain Dsrc Fsrc xs a a).mp hsourcecycle
  have hc1:List.IsChain (fun x y=>Dsrc x y ∧ ¬Fsrc.Adj x y) p1:=by
    apply hc.infix
    refine ⟨[],post++[a],?_⟩
    simp [p1,hxs,List.append_assoc]
  have hc2:List.IsChain (fun x y=>Dsrc x y ∧ ¬Fsrc.Adj x y) p2:=by
    apply hc.infix
    refine ⟨a::pre,[],?_⟩
    simp [p2,hxs,List.append_assoc]
  have hf1:∀ x∈p1,x∉A₀ k→x∉st.assigned k:=by intro x hx;exact hfree x (hmem1 x hx)
  have hs1:∀ x∈p1,x∈QV k:=by intro x hx;exact hsubset x (hmem1 x hx)
  obtain ⟨mid,hm,hmLocal,hmExact,hmA,hmE,hmPres,hmL,_,hmArcs,hmVertices,hmEdges⟩:=
    prescribed_ordered_path_family_restricted_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
      hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext H aScale κ θ haScale hκ hθ hH hθbudget hQlocal hδstrong hnstrong p1 hp1 hc1 st hvalid hLocal hinit hf1 hs1
  have hinitmid:prescribedInducedSourceEdges (Q k) (A₀ k)⊆mid.sourceEdges k:=hinit.trans (hmE k)
  have hf2:∀ x∈p2,x∉A₀ k→x∉mid.assigned k:=by
    intro x hx hnot hmid
    rw [hmExact,Function.update_self] at hmid
    rcases Finset.mem_union.mp hmid with hold'|hnew
    · exact hfree x (hmem2 x hx) hnot hold'
    · have hh:=hinter x (List.mem_toFinset.mp hnew) hx
      rcases hh with rfl|rfl <;> contradiction
  have hs2:∀ x∈p2,x∈QV k:=by intro x hx;exact hsubset x (hmem2 x hx)
  obtain ⟨last,hl,hlLocal,hlExact,hlA,hlE,hlPres,hlL,_,hlArcs,hlVertices,hlEdges⟩:=
    prescribed_ordered_path_family_restricted_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
      hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext H aScale κ θ haScale hκ hθ hH hθbudget hQlocal hδstrong hnstrong p2 hp2 hc2 mid hm hmLocal hinitmid hf2 hs2
  have hunion:p1.toFinset∪p2.toFinset=(a::xs).toFinset:=by
    ext x
    simp only [Finset.mem_union,List.mem_toFinset]
    exact ⟨fun h=>h.elim (hmem1 x) (hmem2 x),hcover x⟩
  refine ⟨last,hl,hlLocal,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hlExact,hmExact]
    funext i
    by_cases hi:i=k
    · subst i
      simp only [Function.update_self,Finset.union_assoc,hunion]
    · simp [Function.update_of_ne hi]
  · intro i;exact (hmA i).trans (hlA i)
  · intro i;exact (hmE i).trans (hlE i)
  · intro i x hx;exact (hlPres i x (hmA i hx)).trans (hmPres i x hx)
  · intro x hx hnot
    rcases hcover x hx with hx1|hx2
    · rw [hlPres k x (hmVertices (List.mem_toFinset.mpr hx1))]
      exact hmL x hx1 hnot
    · exact hlL x hx2 hnot
  · intro e he
    rw [hdirected] at he
    rcases Finset.mem_union.mp he with he1|he2
    · rcases hmArcs e he1 with hboth|hnew
      · exact Or.inl hboth
      · right
        have hend:=prescribed_directed_path_edge_endpoints p1 e he1
        rw [hlPres k e.1 (hmVertices (List.mem_toFinset.mpr hend.1)),
            hlPres k e.2 (hmVertices (List.mem_toFinset.mpr hend.2))]
        exact hnew
    · exact hlArcs e he2
  · intro x hx
    rcases hcover x (List.mem_toFinset.mp hx) with hx1|hx2
    · exact hlA k (hmVertices (List.mem_toFinset.mpr hx1))
    · exact hlVertices (List.mem_toFinset.mpr hx2)
  · rw [hphysical]
    exact Finset.union_subset (hmEdges.trans (hlE k)) hlEdges
end Oberwolfach
