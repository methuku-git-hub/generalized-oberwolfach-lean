module

public import Oberwolfach.PrescribedFamilyState

@[expose] public section
/-! A component update preserves every field of the family state. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I X V:Type} [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_state_step
    (st:PrescribedFamilyState I X V) (QV:I→Finset X) (Q:I→SimpleGraph X)
    (A₀:I→Finset X) (ψ:I→X→V) (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V) (t:ℝ)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J t)
    (k:I) (C:Finset X) (g:X→V) (D:Finset (Sym2 X)) (F:SimpleGraph V)
    (hC:Disjoint C (st.assigned k)) (hCsub:C⊆QV k)
    (hg:Set.InjOn g (↑(st.assigned k∪C):Set X))
    (hpres:∀ x∈st.assigned k,g x=st.vertexMap k x)
    (havoid:∀ x∈C,g x∉Finset.univ.filter
      (fun v=>(t:ℝ)≤(st.freeOccurrences.filter (fun p=>familyVertexImage st.vertexMap p=v)).card))
    (hDsub:D⊆(Q k).edgeFinset)
    (hDends:∀ e∈D,∀ x∈e.toFinset,x∈st.assigned k∪C)
    (hcover:∀ i,st.physicalEdges i⊆F.edgeFinset) (hJ:J.edgeFinset⊆F.edgeFinset)
    (hedges:Disjoint (D.image (Sym2.map g)) F.edgeFinset):
    let added:=D.image (Sym2.map g);
    let st':PrescribedFamilyState I X V:=
      ⟨Function.update st.assigned k (st.assigned k∪C),
       Function.update st.vertexMap k g,st.freeOccurrences∪({k}:Finset I).product C,
       Function.update st.sourceEdges k (st.sourceEdges k∪D),
       Function.update st.physicalEdges k (st.physicalEdges k∪added),
       Function.update st.newEdges k (st.newEdges k∪added)⟩;
    st'.Valid QV Q A₀ ψ E₀ J t := by
  intro added st'
  rcases hvalid with ⟨hinj,hdom,hsubset,hψ,hload,hsource,hends,hrepr,hpair,hE₀,hnew⟩
  have hT:∀ p∈st.freeOccurrences,p.2∈st.assigned p.1:=by
    intro p hp
    exact (hdom p.1 p.2).mpr (Or.inr hp)
  have hfam:=prescribed_family_component_invariant st.assigned st.vertexMap st.freeOccurrences k C g t
    hinj hT hC hg hpres hload havoid st.physicalEdges added F J hpair hcover hJ hedges
  have hdomains:=prescribed_family_domains_update st.assigned A₀ st.freeOccurrences k C hdom
  have hedges':=prescribed_family_source_edge_update st.assigned st.vertexMap Q st.sourceEdges st.physicalEdges
    hrepr hsource hends k C g D hpres hDsub hDends
  refine ⟨hfam.1,hdomains,?_,?_,hfam.2.2.2.1,hedges'.2.1,hedges'.2.2,hedges'.1,hfam.2.2.2.2.1,?_,?_⟩
  · intro i x hx
    by_cases hi:i=k
    · subst i
      have hx':x∈st.assigned k∪C:=by simpa [st',Function.update_self] using hx
      rcases Finset.mem_union.mp hx' with hx'|hx'
      · exact hsubset k hx'
      · exact hCsub hx'
    · have hx':x∈st.assigned i:=by simpa [st',Function.update_of_ne hi] using hx
      exact hsubset i hx'
  · intro i x hx
    have hxA:x∈st.assigned i:=(hdom i x).mpr (Or.inl hx)
    exact (hfam.2.1 i x hxA).trans (hψ i x hx)
  · intro i
    by_cases hi:i=k
    · subst i
      simp only [st',Function.update_self]
      rw [hE₀ k]
      exact Finset.union_assoc _ _ _
    · simpa [st',Function.update_of_ne hi] using hE₀ i
  · intro i
    by_cases hi:i=k
    · subst i
      simp only [st',Function.update_self]
      exact Finset.disjoint_union_left.mpr ⟨hnew k,hfam.2.2.2.2.2⟩
    · simpa [st',Function.update_of_ne hi] using hnew i
end Oberwolfach
