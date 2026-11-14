module

public import Oberwolfach.OrdinaryActualAttachmentIdentity
public import Oberwolfach.ResourceDecompositionCounts
public import Oberwolfach.OrdinaryDecompositionEdges

@[expose] public section

/-! The old-edge contribution in identity (A) is the difference of the
actual physical root-edge sets. Edge injectivity, rather than injectivity
on vertices, is exactly what is required to preserve multiplicity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem injective_image_integer_indicator {I X:Type} [Fintype I] [DecidableEq I] [DecidableEq X]
    (f:I→X) (hf:Function.Injective f) (x:X):
    (∑ i,if x=f i then (1:ℤ) else 0)=if x∈Finset.univ.image f then 1 else 0:=by
  have hd:∀ i∈(Finset.univ:Finset I),∀ j∈(Finset.univ:Finset I),i≠j→Disjoint ({f i}:Finset X) {f j}:=by
    intro i _ j _ hij
    simpa only [Finset.disjoint_singleton] using (show f i≠f j from fun he=>hij (hf he))
  have hs:Finset.univ.biUnion (fun i=>({f i}:Finset X))=Finset.univ.image f:=by ext;simp [eq_comm]
  have hh:=resource_decomposition_indicator (fun i=>({f i}:Finset X)) Finset.univ (Finset.univ.image f) hd hs x
  simp only [Finset.mem_singleton] at hh
  exact_mod_cast hh

 theorem physical_delta_sum {I X:Type} [Fintype I] [DecidableEq I] [DecidableEq X]
    (f g:I→X) (hf:Function.Injective f) (hg:Function.Injective g) (x:X):
    (∑ i,physicalIntDelta (f i) (g i) x)=
      (if x∈Finset.univ.image f then (1:ℤ) else 0)-(if x∈Finset.univ.image g then 1 else 0):=by
  simp only [physicalIntDelta,Finset.sum_sub_distrib,injective_image_integer_indicator _ hf,
    injective_image_integer_indicator _ hg]

 def transformerImageResources (G:SimpleGraph V) (H₀:V→U→Prop) (φ:V→V) (ψ:U→U):Finset (Sym2 V⊕(V×U)):=
  (Finset.univ.image (fun i:G.edgeFinset=>Sum.inl s(φ i.val.out.1,φ i.val.out.2)))∪
  (Finset.univ.image (fun i:{e:V×U // H₀ e.1 e.2}=>Sum.inr (φ i.val.1,ψ i.val.2)))

 theorem transformer_original_edge_identity (G:SimpleGraph V) (H₀:V→U→Prop) (φ:V→V) (ψ:U→U)
    (hφ:Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2)))
    (hψ:Function.Injective (fun i:{e:V×U // H₀ e.1 e.2}=>(φ i.val.1,ψ i.val.2)))
    (e:Sym2 V⊕(V×U)):
    (∑ i:G.edgeFinset,physicalIntDelta (.inl i.val) (.inl s(φ i.val.out.1,φ i.val.out.2)) e)+
    (∑ i:{e:V×U // H₀ e.1 e.2},physicalIntDelta (.inr i.val) (.inr (φ i.val.1,ψ i.val.2)) e)=
    (if e∈ordinaryHostResources G H₀ then (1:ℤ) else 0)-
      (if e∈transformerImageResources G H₀ φ ψ then 1 else 0):=by
  have h1:=physical_delta_sum
    (fun i:G.edgeFinset=>(Sum.inl i.val:Sym2 V⊕(V×U)))
    (fun i:G.edgeFinset=>(Sum.inl s(φ i.val.out.1,φ i.val.out.2):Sym2 V⊕(V×U)))
    (by intro i j he;exact Subtype.ext (Sum.inl.inj he)) (by intro i j he;exact hφ (Sum.inl.inj he)) e
  have h2:=physical_delta_sum
    (fun i:{e:V×U // H₀ e.1 e.2}=>(Sum.inr i.val:Sym2 V⊕(V×U)))
    (fun i:{e:V×U // H₀ e.1 e.2}=>(Sum.inr (φ i.val.1,ψ i.val.2):Sym2 V⊕(V×U)))
    (by intro i j he;exact Subtype.ext (Sum.inr.inj he)) (by intro i j he;exact hψ (Sum.inr.inj he)) e
  rw [h1,h2]
  cases e with
  | inl e=>
    have hmem:e∈G.edgeSet↔e∈G.edgeFinset:=SimpleGraph.mem_edgeFinset.symm
    simp only [transformerImageResources,ordinaryHostResources_rim,Finset.mem_union,Finset.mem_image,
      Finset.mem_univ,true_and,Sum.inl.injEq,Sum.inr_ne_inl,exists_false,or_false,hmem]
    have hex:(∃ i:G.edgeFinset,i.val=e)↔e∈G.edgeFinset:=by
      constructor
      · rintro ⟨i,rfl⟩;exact i.property
      · intro h;exact ⟨⟨e,h⟩,rfl⟩
    simp only [hex,ite_false,sub_self,add_zero]
  | inr vu=>
    rcases vu with ⟨v,u⟩
    have hex:(∃ i:{e:V×U // H₀ e.1 e.2},i.val=(v,u))↔H₀ v u:=by
      constructor
      · rintro ⟨i,he⟩;have hi:=i.property;simpa only [he] using hi
      · intro h;exact ⟨⟨(v,u),h⟩,rfl⟩
    simp only [transformerImageResources,ordinaryHostResources_spoke,Finset.mem_union,Finset.mem_image,
      Finset.mem_univ,true_and,Sum.inr.injEq,Sum.inl_ne_inr,exists_false,false_or,hex,
      ite_false,sub_self,zero_add]

end Oberwolfach
