module

public import Oberwolfach.InvariantPermutation
public import Oberwolfach.MarkedProtectedActiveGeometry

@[expose] public section

/-! The active complements and the remaining inner rows are actual
subtypes of the original vertex sets. Their embeddings and restricted
permutations are constructed, with exact images. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_protected_canonical_domains
    (π:Equiv.Perm V) (I T:Finset V) (J W:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T):
    let A:Type:={x:V//x∉T}
    let B:Type:={u:U//u∉W}
    let C:Type:={x:V//x∈I\T};
    ∃ (f:A↪oV) (g:B↪U) (i:C↪oA) (ρA:Equiv.Perm A) (ρ:Equiv.Perm C),
    (∀ x,f (ρA x)=π (f x))∧(∀ x,i (ρ x)=ρA (i x))∧
    Finset.univ.image f=Finset.univ\T∧Finset.univ.image g=Finset.univ\W∧
    let X:=Finset.univ.image i
    let Z:=Finset.univ.filter (fun u:B=>g u∈J);
    X.image f=I\T∧Z.image g=J\W∧
    (∀ x,f x∈I↔x∈X)∧(∀ u,g u∈J↔u∈Z)∧
    (∀ x,ρA x∈X↔x∈X)∧
    (∀ x,(i.comp f) x=x.val)∧
    Fintype.card A=Fintype.card V-T.card∧Fintype.card B=Fintype.card U-W.card∧
    Fintype.card C=(I\T).card:=by
  intro A B C
  let f:A↪oV:=OrderEmbedding.subtype (fun x:V=>x∉T)
  let g:B↪U:=Function.Embedding.subtype (fun u:U=>u∉W)
  let i:C↪oA:=
    { toFun := fun x => ⟨x.val,(Finset.mem_sdiff.mp x.property).2⟩
      inj' := fun x y h => Subtype.ext (congrArg (fun z:A=>z.val) h)
      map_rel_iff' := Iff.rfl }
  have hAinv:∀ x,π x∈({x:V|x∉T}:Set V)↔x∈({x:V|x∉T}:Set V):=by
    intro x;exact not_congr (hT x)
  have hCinv:∀ x,π x∈({x:V|x∈I\T}:Set V)↔x∈({x:V|x∈I\T}:Set V):=by
    intro x;simp only [Set.mem_setOf_eq,Finset.mem_sdiff,hI,hT]
  let ρA:=invariantSetPermutation π {x:V|x∉T} hAinv
  let ρ:=invariantSetPermutation π {x:V|x∈I\T} hCinv
  have hf:∀ x,f (ρA x)=π (f x):=fun _=>rfl
  have hi:∀ x,i (ρ x)=ρA (i x):=fun _=>Subtype.ext rfl
  have himg:Finset.univ.image f=Finset.univ\T:=by
    ext x;simp only [Finset.mem_image,Finset.mem_univ,Finset.mem_sdiff,true_and]
    exact ⟨fun ⟨y,hy⟩=>hy ▸ y.property,fun hx=>⟨⟨x,hx⟩,rfl⟩⟩
  have gimg:Finset.univ.image g=Finset.univ\W:=by
    ext u;simp only [Finset.mem_image,Finset.mem_univ,Finset.mem_sdiff,true_and]
    exact ⟨fun ⟨v,hv⟩=>hv ▸ v.property,fun hu=>⟨⟨u,hu⟩,rfl⟩⟩
  refine ⟨f,g,i,ρA,ρ,hf,hi,himg,gimg,?_⟩
  intro X Z
  have hx:∀ x:A,f x∈I↔x∈X:=by
    intro x
    constructor
    · intro h
      exact Finset.mem_image.mpr ⟨⟨x.val,Finset.mem_sdiff.mpr ⟨h,x.property⟩⟩,Finset.mem_univ _,Subtype.ext rfl⟩
    · intro h
      obtain ⟨y,_,rfl⟩:=Finset.mem_image.mp h
      exact (Finset.mem_sdiff.mp y.property).1
  have hz:∀ u:B,g u∈J↔u∈Z:=by intro u;simp only [Z,Finset.mem_filter,Finset.mem_univ,true_and]
  have hXimage:X.image f=I\T:=by
    ext x
    constructor
    · rintro h
      obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp h
      exact Finset.mem_sdiff.mpr ⟨(hx y).mpr hy,y.property⟩
    · intro h
      exact Finset.mem_image.mpr ⟨⟨x,(Finset.mem_sdiff.mp h).2⟩,(hx _).mp (Finset.mem_sdiff.mp h).1,rfl⟩
  have hZimage:Z.image g=J\W:=by
    ext u
    constructor
    · rintro h
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp h
      exact Finset.mem_sdiff.mpr ⟨(hz v).mpr hv,v.property⟩
    · intro h
      exact Finset.mem_image.mpr ⟨⟨u,(Finset.mem_sdiff.mp h).2⟩,(hz _).mp (Finset.mem_sdiff.mp h).1,rfl⟩
  refine ⟨hXimage,hZimage,hx,hz,?_,fun _=>rfl,?_,?_,?_⟩
  · intro x;rw [←hx,←hx,hf,hI]
  · have hh:=congrArg Finset.card himg
    rw [Finset.card_image_of_injective _ f.injective,Finset.card_univ,
      Finset.card_sdiff_of_subset (Finset.subset_univ T),Finset.card_univ] at hh
    exact hh
  · have hh:=congrArg Finset.card gimg
    rw [Finset.card_image_of_injective _ g.injective,Finset.card_univ,
      Finset.card_sdiff_of_subset (Finset.subset_univ W),Finset.card_univ] at hh
    exact hh
  · exact Fintype.card_coe (I\T)

end Oberwolfach
