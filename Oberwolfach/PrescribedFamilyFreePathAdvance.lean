module

public import Oberwolfach.PrescribedFamilyResources
public import Oberwolfach.PrescribedFamilyStateStep
public import Oberwolfach.PrescribedSourceComponentEdges
public import Oberwolfach.PrescribedComponentSourceEndpoints
public import Oberwolfach.PrescribedFreeComponentSteps

@[expose] public section
/-! Embed one actual source path with no prescribed vertex and update the complete family
state using only the original quantitative resources. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_free_path_advance
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
    (k:I) (as:List X) (has:as.Nodup) (hlen:1≤as.length)
    (hfree:∀ x∈as,x∉st.assigned k) (hsubset:∀ x∈as,x∈QV k)
    (Dsrc:X→X→Prop) (Fsrc:SimpleGraph X)
    (hDQ:∀ x y,Dsrc x y→(Q k).Adj x y)
    (hsrc:DirectedNonemptyPath Dsrc Fsrc true as)
    (D:V→V→Prop) (L:Finset V) (hext:IsExtendingList D L β):
    ∃ (g:X→V) (F:SimpleGraph V),
      let C:=as.toFinset;
      let Es:=prescribedFreePathPhysicalEdges as;
      let added:=Es.image (Sym2.map g);
      let st':PrescribedFamilyState I X V:=
        ⟨Function.update st.assigned k (st.assigned k∪C),
         Function.update st.vertexMap k g,st.freeOccurrences∪({k}:Finset I).product C,
         Function.update st.sourceEdges k (st.sourceEdges k∪Es),
         Function.update st.physicalEdges k (st.physicalEdges k∪added),
         Function.update st.newEdges k (st.newEdges k∪added)⟩;
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀ x∈st.assigned k,g x=st.vertexMap k x) ∧
      DirectedNonemptyPath D F true (as.map g) ∧
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
  have hb:= (hbudget k as has hsub hdis).1
  obtain ⟨g,hg,hpres,hlist,hpath,_⟩:=prescribed_free_path_component_step as has hlen (st.assigned k) (st.vertexMap k)
    (hvalid.1 k) hfree S L β D hext F J (8*Real.sqrt δ*n) hM hF hb
    st.physicalEdges k hvalid.2.2.2.2.2.2.2.2.1 hEF hJF
  have hCdis:Disjoint as.toFinset (st.assigned k):=hdis.symm
  have hCsub:as.toFinset⊆QV k:=by intro x hx;exact hsubset x (List.mem_toFinset.mp hx)
  have hav:∀ x∈as.toFinset,g x∉S:=by intro x hx;exact (hlist x (List.mem_toFinset.mp hx)).2
  have hsrcE:=prescribed_free_path_source_edges Dsrc (Q k) Fsrc hDQ as hsrc
  have hends:∀ e∈prescribedFreePathPhysicalEdges as,∀ x∈e.toFinset,x∈st.assigned k∪as.toFinset:=by
    intro e he x hx
    exact Finset.mem_union_right _ (prescribed_free_path_component_endpoints as e he x hx)
  have heavoid:Disjoint ((prescribedFreePathPhysicalEdges as).image (Sym2.map g)) F.edgeFinset:=by
    rw [prescribed_free_path_physical_map]
    exact prescribed_free_path_physical_avoid D F (as.map g) hpath
  refine ⟨g,F,?_,hpres,hpath,?_⟩
  · exact prescribed_family_state_step st QV Q A₀ ψ E₀ J (Real.sqrt δ*n) hvalid k as.toFinset g
      (prescribedFreePathPhysicalEdges as) F hCdis hCsub hg hpres hav hsrcE hends hEF hJF heavoid
  · intro x hx;exact (hlist x hx).1
end Oberwolfach
