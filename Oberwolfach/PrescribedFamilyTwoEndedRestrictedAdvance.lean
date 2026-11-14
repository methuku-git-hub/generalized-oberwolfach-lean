module

public import Oberwolfach.PrescribedRestrictedLoadStep
public import Oberwolfach.PrescribedFamilyResources
public import Oberwolfach.PrescribedFamilyStateStep
public import Oberwolfach.PrescribedSourcePathEdges
public import Oberwolfach.PrescribedComponentSourceEndpoints
public import Oberwolfach.PrescribedAnchoredComponentSteps

@[expose] public section
/-! Embed one actual two-ended source path and update the complete family
state using only the original quantitative resources. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_two_ended_restricted_advance
    (st:PrescribedFamilyState I X V) (QV:I→Finset X) (Q:I→SimpleGraph X)
    (A₀:I→Finset X) (ψ:I→X→V) (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hQsize:∀ i,((QV i).card:ℝ)≤δ*Fintype.card V)
    (hQdegree:∀ i x,(Q i).degree x≤2)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V))
    (k:I) (a b:X) (as:List X) (has:as.Nodup) (hlen:1≤as.length)
    (ha:a∈st.assigned k) (hb:b∈st.assigned k) (hab:a≠b)
    (hfree:∀ x∈as,x∉st.assigned k) (hsubset:∀ x∈as,x∈QV k)
    (Dsrc:X→X→Prop) (Fsrc:SimpleGraph X)
    (hDQ:∀ x y,Dsrc x y→(Q k).Adj x y)
    (hsrc:DirectedPathThrough Dsrc Fsrc a b as)
    (D:V→V→Prop) (L:Finset V) (hext:IsExtendingList D L β)
    (H:Finset I) (tLocal:ℝ) (Slocal:Finset V)
    (hLocal:∀v,(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤tLocal+1)
    (hSat:∀v,tLocal≤(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)→v∈Slocal)
    (hroom:(((st.assigned k).image (st.vertexMap k) ∪
      ((Finset.univ.filter (fun v=>(Real.sqrt δ*Fintype.card V:ℝ)≤
        (st.freeOccurrences.filter (fun p=>familyVertexImage st.vertexMap p=v)).card))∪Slocal)).card:ℝ)+
      as.length+2+2*(8*Real.sqrt δ*Fintype.card V)<β*Fintype.card V):
    ∃ (g:X→V) (F:SimpleGraph V),
      let C:=as.toFinset;
      let Es:=prescribedPathPhysicalEdges a b as;
      let added:=Es.image (Sym2.map g);
      let st':PrescribedFamilyState I X V:=
        ⟨Function.update st.assigned k (st.assigned k∪C),
         Function.update st.vertexMap k g,st.freeOccurrences∪({k}:Finset I).product C,
         Function.update st.sourceEdges k (st.sourceEdges k∪Es),
         Function.update st.physicalEdges k (st.physicalEdges k∪added),
         Function.update st.newEdges k (st.newEdges k∪added)⟩;
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀v,(((st'.freeOccurrences.filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st'.vertexMap p=v)).card:ℝ)≤tLocal+1) ∧
      (∀ x∈st.assigned k,g x=st.vertexMap k x) ∧
      DirectedPathThrough D F (g a) (g b) (as.map g) ∧
      ∀ x∈as,g x∈L := by
  let n:ℝ:=Fintype.card V
  let S:Finset V:=Finset.univ.filter (fun v=>(Real.sqrt δ*n:ℝ)≤
    (st.freeOccurrences.filter (fun p=>familyVertexImage st.vertexMap p=v)).card)
  have hdis:Disjoint (st.assigned k) as.toFinset:=by
    apply Finset.disjoint_left.mpr
    intro x hx hxs
    exact hfree x (List.mem_toFinset.mp hxs) hx
  have hsub:st.assigned k∪as.toFinset⊆QV k:=by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hvalid.2.2.1 k hx
    · exact hsubset x (List.mem_toFinset.mp hx)
  obtain ⟨hS,F,hF,hJF,hEF,hbudget⟩:=prescribed_family_state_resources st QV Q A₀ ψ E₀ J β δ n
    hβ hβ1 hδ hδbound hnβ hn hI hQsize hQdegree hold hJ hvalid
  have hM:0≤8*Real.sqrt δ*n:=by
    have hroot:0<Real.sqrt δ:=Real.sqrt_pos.2 hδ
    have hnpos:0<n:=by have :0<2/Real.sqrt δ:=div_pos (by norm_num) hroot;linarith
    positivity
  have hbudget2:= (hbudget k as has hsub hdis).2.2.1
  obtain ⟨g,hg,hpres,hlist,hpath,_⟩:=prescribed_two_ended_component_step as has hlen (st.assigned k) (st.vertexMap k)
    (hvalid.1 k) hfree a b ha hb hab (S∪Slocal) L β D hext F J (8*Real.sqrt δ*n) hM hF (by simpa only [S,n] using hroom)
    st.physicalEdges k hvalid.2.2.2.2.2.2.2.2.1 hEF hJF
  have hCdis:Disjoint as.toFinset (st.assigned k):=hdis.symm
  have hCsub:as.toFinset⊆QV k:=by intro x hx;exact hsubset x (List.mem_toFinset.mp hx)
  have hav:∀ x∈as.toFinset,g x∉S:=by
    intro x hx hs
    exact (hlist x (List.mem_toFinset.mp hx)).2 (Finset.mem_union_left _ hs)
  have havLocal:∀ x∈as.toFinset,g x∉Slocal:=by
    intro x hx hs
    exact (hlist x (List.mem_toFinset.mp hx)).2 (Finset.mem_union_right _ hs)
  have hsrcE:=prescribed_two_ended_source_edges Dsrc (Q k) Fsrc hDQ b as a hsrc
  have hends:=prescribed_two_ended_component_endpoints (st.assigned k) a b ha hb as
  have heavoid:=prescribed_two_ended_mapped_edges_avoid g D F a b as hpath
  have hT:∀p∈st.freeOccurrences,p.2∈st.assigned p.1:=by
    intro p hp
    exact (hvalid.2.1 p.1 p.2).mpr (Or.inr hp)
  have hTdis:Disjoint st.freeOccurrences (({k}:Finset I).product as.toFinset):=by
    apply Finset.disjoint_left.mpr
    intro p hp hprod
    have hh:=Finset.mem_product.mp hprod
    have hk:p.1=k:=by simpa using hh.1
    have hAssigned:=hT p hp
    rw [hk] at hAssigned
    exact (Finset.disjoint_left.mp hCdis) hh.2 hAssigned
  let f':=Function.update st.vertexMap k g
  have hpresAll:∀p∈st.freeOccurrences,familyVertexImage f' p=familyVertexImage st.vertexMap p:=by
    intro p hp
    by_cases hi:p.1=k
    · have hm:p.2∈st.assigned k:=by simpa only [hi] using hT p hp
      simpa only [familyVertexImage,f',hi,Function.update_self] using hpres p.2 hm
    · simp only [familyVertexImage,f',Function.update_of_ne hi]
  have hnewinj:Set.InjOn (familyVertexImage f') (↑(({k}:Finset I).product as.toFinset):Set (I×X)):=by
    intro p hp q hq he
    have hp':=Finset.mem_product.mp hp
    have hq':=Finset.mem_product.mp hq
    have hpk:p.1=k:=by simpa using hp'.1
    have hqk:q.1=k:=by simpa using hq'.1
    rcases p with ⟨i,x⟩
    rcases q with ⟨j,y⟩
    simp only at hpk hqk
    subst i
    subst j
    simp only [familyVertexImage,f',Function.update_self] at he
    have hxy:x=y:=hg (by exact Finset.mem_union_right _ hp'.2) (by exact Finset.mem_union_right _ hq'.2) he
    subst y
    rfl
  have hlocalAvoid:∀p∈(({k}:Finset I).product as.toFinset),p.1∈H→
      familyVertexImage f' p∉Finset.univ.filter (fun v=>(tLocal:ℝ)≤
        ((st.freeOccurrences.filter (fun p=>p.1∈H)).filter (fun y=>familyVertexImage st.vertexMap y=v)).card):=by
    intro p hp _ hs
    have hh:=Finset.mem_product.mp hp
    have hk:p.1=k:=by simpa using hh.1
    have hSat':familyVertexImage f' p∈Slocal:=hSat _ (Finset.mem_filter.mp hs).2
    change f' p.1 p.2∈Slocal at hSat'
    rw [hk] at hSat'
    simp only [f',Function.update_self] at hSat'
    exact havLocal p.2 hh.2 hSat'
  have hLocalStep:=prescribed_restricted_component_load_step st.freeOccurrences
    (({k}:Finset I).product as.toFinset) (fun p=>p.1∈H) (familyVertexImage st.vertexMap)
    (familyVertexImage f') tLocal hTdis hpresAll hnewinj
    (by convert hLocal using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hlocalAvoid using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
  refine ⟨g,F,?_,?_,hpres,hpath,?_⟩
  · exact prescribed_family_state_step st QV Q A₀ ψ E₀ J (Real.sqrt δ*n) hvalid k as.toFinset g
      (prescribedPathPhysicalEdges a b as) F hCdis hCsub hg hpres hav hsrcE hends hEF hJF heavoid
  · convert hLocalStep using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · intro x hx;exact (hlist x hx).1
end Oberwolfach
