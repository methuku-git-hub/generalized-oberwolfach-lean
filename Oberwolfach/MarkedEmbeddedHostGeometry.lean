module

public import Oberwolfach.MarkedEmbeddedHubCycles

@[expose] public section

/-! Physical edges and spoke classes of an embedded inner host retain
injectivity, type separation, and their exact cardinalities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W V U E K:Type} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]

theorem markedPhysicalEdge_embedding (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W) (a:E⊕K):
    markedPhysicalEdge (f∘tail) (f∘head) (f∘ktail) (f∘khead) π a=
      (markedPhysicalEdge tail head ktail khead ρ a).image f:=by
  cases a <;> simp only [markedPhysicalEdge,Sum.elim_inl,Sum.elim_inr,Function.comp_apply,
    Finset.image_insert,Finset.image_singleton,h]

theorem markedPhysicalEdge_embedding_injective (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (hi:Function.Injective (markedPhysicalEdge tail head ktail khead ρ)):
    Function.Injective (markedPhysicalEdge (f∘tail) (f∘head) (f∘ktail) (f∘khead) π):=by
  intro a b hab
  rw [markedPhysicalEdge_embedding f ρ π h,markedPhysicalEdge_embedding f ρ π h] at hab
  exact hi (Finset.image_injective f.injective hab)

theorem spokeRelationImage_disjoint (f:W↪V) (H₀ HK:W→U→Prop) (u:U)
    (h:∀ x,¬(H₀ x u∧HK x u)):∀ v,¬(spokeRelationImage f H₀ v u∧spokeRelationImage f HK v u):=by
  rintro v ⟨⟨x,hx,hxH⟩,⟨y,hy,hyH⟩⟩
  have he:x=y:=f.injective (hx.trans hy.symm)
  exact h x ⟨hxH,he.symm ▸ hyH⟩

theorem spokeRelationImage_separated (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (H₀ HK:W→U→Prop) (u:U)
    (hs:∀ x y,H₀ x u→HK y u→x≠ρ y):
    ∀ v z,spokeRelationImage f H₀ v u→spokeRelationImage f HK z u→v≠π z:=by
  rintro v z ⟨x,hx,hxH⟩ ⟨y,hy,hyH⟩ he
  apply hs x y hxH hyH
  apply f.injective
  rw [h,hx,hy]
  exact he

theorem spokeRelationImage_neighbourhood (f:W↪V) (H₀ HK:W→U→Prop) (u:U):
    Finset.univ.filter (fun v=>spokeRelationImage f H₀ v u∨spokeRelationImage f HK v u)=
      (Finset.univ.filter (fun x=>H₀ x u∨HK x u)).image f:=by
  ext v
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image,spokeRelationImage]
  constructor
  · rintro (⟨x,hx,hH⟩|⟨x,hx,hH⟩)
    · exact ⟨x,Or.inl hH,hx⟩
    · exact ⟨x,Or.inr hH,hx⟩
  · rintro ⟨x,hH,hx⟩
    rcases hH with hH|hH
    · exact Or.inl ⟨x,hx,hH⟩
    · exact Or.inr ⟨x,hx,hH⟩

theorem spokeRelationImage_neighbourhood_card (f:W↪V) (H₀ HK:W→U→Prop) (u:U):
    (Finset.univ.filter (fun v=>spokeRelationImage f H₀ v u∨spokeRelationImage f HK v u)).card=
      (Finset.univ.filter (fun x=>H₀ x u∨HK x u)).card:=by
  rw [spokeRelationImage_neighbourhood,Finset.card_image_of_injective _ f.injective]

end Oberwolfach
