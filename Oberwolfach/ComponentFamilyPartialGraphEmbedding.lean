module

public import Oberwolfach.ComponentFamilyPartialEmbedding

@[expose] public section
/-! Gluing component maps also maps every source edge in the union to an
edge of the corresponding selected target piece. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {A:Type}

theorem component_family_partial_graph_embedding
    (F:SimpleGraph (Fin n)) (C:A→F.ConnectedComponent)
    (hC:Function.Injective C) (f:∀a,C a↪Fin n)
    (hdis:∀a b,a≠b→Disjoint (Finset.univ.image (f a)) (Finset.univ.image (f b)))
    (R:A→Fin n→Fin n→Prop)
    (hR:∀a (x y:C a),(C a).toSimpleGraph.Adj x y→R a (f a x) (f a y)):
    ∃ψ:{v:Fin n // ∃a,v∈(C a).supp}↪Fin n,
      (∀a (x:C a),ψ ⟨x.val,⟨a,x.property⟩⟩=f a x) ∧
      (∀x y,F.Adj x.val y.val→∃a,R a (ψ x) (ψ y)) :=by
  obtain ⟨ψ,hψ⟩:=component_family_partial_embedding F C hC f hdis
  refine ⟨ψ,hψ,?_⟩
  intro x y hxy
  obtain ⟨a,hx⟩:=x.property
  have hy:y.val∈(C a).supp:=(C a).mem_supp_of_adj_mem_supp hx hxy
  let x':C a:=⟨x.val,hx⟩
  let y':C a:=⟨y.val,hy⟩
  have hxψ:ψ x=f a x':=by
    have h:=hψ a x'
    convert h using 1 <;> congr 1
  have hyψ:ψ y=f a y':=by
    have h:=hψ a y'
    convert h using 1 <;> congr 1
  refine ⟨a,?_⟩
  rw [hxψ,hyψ]
  exact hR a x' y' hxy
end Oberwolfach
