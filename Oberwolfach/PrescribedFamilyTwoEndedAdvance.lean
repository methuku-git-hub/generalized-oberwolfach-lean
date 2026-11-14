module

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

theorem prescribed_family_two_ended_advance
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
    (D:V→V→Prop) (L:Finset V) (hext:IsExtendingList D L β):
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
    (hvalid.1 k) hfree a b ha hb hab S L β D hext F J (8*Real.sqrt δ*n) hM hF hbudget2
    st.physicalEdges k hvalid.2.2.2.2.2.2.2.2.1 hEF hJF
  have hCdis:Disjoint as.toFinset (st.assigned k):=hdis.symm
  have hCsub:as.toFinset⊆QV k:=by intro x hx;exact hsubset x (List.mem_toFinset.mp hx)
  have hav:∀ x∈as.toFinset,g x∉S:=by intro x hx;exact (hlist x (List.mem_toFinset.mp hx)).2
  have hsrcE:=prescribed_two_ended_source_edges Dsrc (Q k) Fsrc hDQ b as a hsrc
  have hends:=prescribed_two_ended_component_endpoints (st.assigned k) a b ha hb as
  have heavoid:=prescribed_two_ended_mapped_edges_avoid g D F a b as hpath
  refine ⟨g,F,?_,hpres,hpath,?_⟩
  · exact prescribed_family_state_step st QV Q A₀ ψ E₀ J (Real.sqrt δ*n) hvalid k as.toFinset g
      (prescribedPathPhysicalEdges a b as) F hCdis hCsub hg hpres hav hsrcE hends hEF hJF heavoid
  · intro x hx;exact (hlist x hx).1
end Oberwolfach
