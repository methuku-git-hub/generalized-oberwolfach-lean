module

public import Oberwolfach.ResidualActualEmbeddingGlue

@[expose] public section
/-! Glue the old and residual maps only on the complement of the final path
interiors, leaving those interiors free for later reconstruction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_embeddings_glue_on_complement
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Nonempty V]
    [DecidableEq K] [DecidableEq J] {F:SimpleGraph X}
    (data:ActualResidualData (K:=K) (J:=J) F) (hF:F.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (D:Finset X) (hDR:Disjoint D data.remaining)
    (ψ:X→V) (hψ:Set.InjOn ψ (↑(data.oldDomain\D):Set X))
    (B:Finset {x // x∈data.remaining})
    (g Φ:{x // x∈data.remaining}→V) (L C Z:Finset V)
    (hA₀B:residualSubtypeSet data.remaining data.prescribed⊆B)
    (hΦ:Function.Injective Φ)
    (hg:∀x∈residualSubtypeSet data.remaining data.prescribed,g x=ψ x.val)
    (hΦg:∀x∈B,Φ x=g x)
    (himage:B.image g=(residualSubtypeSet data.remaining data.prescribed).image (fun x=>ψ x.val)∪C∪Z)
    (hOldC:Disjoint ((data.oldDomain\D).image ψ) C)
    (hOldZ:Disjoint ((data.oldDomain\D).image ψ) Z)
    (hfree:∀x,x∉B→Φ x∈L) (hL:Disjoint L ((data.oldDomain\D).image ψ)):
    ∃fC:{x // x∉D}↪V,
      (∀x:{x // x∉D},x.val∈data.oldDomain→fC x=ψ x.val) ∧
      (∀x:{x // x∈data.remaining},∀hx:x.val∉D,fC ⟨x.val,hx⟩=Φ x):=by
  classical
  let Old:=data.oldDomain\D
  let embed:{x // x∈data.remaining}↪X:=⟨Subtype.val,Subtype.val_injective⟩
  have hOverlap:Old∩data.remaining=data.prescribed:=by
    ext x
    have hOldR: x∈data.oldDomain∩data.remaining ↔ x∈data.prescribed :=by
      rw [(data.graph_facts hF).2.2.2.2.2]
    have hNo:x∈data.remaining→x∉D:=by
      intro hr hd
      exact Finset.disjoint_left.mp hDR hd hr
    simp only [Old,Finset.mem_inter,Finset.mem_sdiff] at *
    constructor
    · rintro ⟨⟨ho,hn⟩,hr⟩
      exact hOldR.mp ⟨ho,hr⟩
    · intro hp
      obtain ⟨ho,hr⟩:=hOldR.mpr hp
      exact ⟨⟨ho,hNo hr⟩,hr⟩
  have hA₀:∀x:{x // x∈data.remaining},
      x∈residualSubtypeSet data.remaining data.prescribed↔embed x∈Old:=
    (residual_subtype_glue_inputs data.remaining data.prescribed Old hOverlap ψ hψ).1
  have hIm:(Finset.univ.image embed)=data.remaining:=by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    change (∃y:{y // y∈data.remaining},y.val=x) ↔ x∈data.remaining
    exact ⟨fun ⟨y,hy⟩=>hy ▸ y.property,fun hx=>⟨⟨x,hx⟩,rfl⟩⟩
  have hCover:Old∪data.remaining=Finset.univ\D:=by
    ext x
    have hor:x∈data.oldDomain ∨ x∈data.remaining:=by
      have hh:x∈data.oldDomain∪data.remaining:=by rw [data.old_domain_union_remaining hCycle];exact Finset.mem_univ _
      exact Finset.mem_union.mp hh
    have hNo:x∈data.remaining→x∉D:=by
      intro hr hd
      exact Finset.disjoint_left.mp hDR hd hr
    simp only [Old,Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
    constructor
    · rintro (⟨_,hn⟩|hr)
      · exact hn
      · exact hNo hr
    · intro hn
      rcases hor with ho | hr
      · exact Or.inl ⟨ho,hn⟩
      · exact Or.inr hr
  obtain ⟨h,hinj,hold,hres⟩:=prescribed_subtype_complete_factor_glue
    embed Old (residualSubtypeSet data.remaining data.prescribed) B ψ (fun x=>ψ x.val) g Φ L C Z
    hA₀ hA₀B hψ hΦ (by intro x hx;rfl) hg hΦg himage hOldC hOldZ hfree hL
  rw [hIm,hCover] at hinj
  let fC:{x // x∉D}↪V:=⟨fun x=>h x.val,by
    intro x y heq
    apply Subtype.ext
    exact hinj (by simpa using x.property) (by simpa using y.property) heq⟩
  refine ⟨fC,?_,?_⟩
  · intro x hx
    exact hold x.val (Finset.mem_sdiff.mpr ⟨hx,x.property⟩)
  · intro x hx
    exact hres x
end Oberwolfach
