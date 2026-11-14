module

public import Oberwolfach.InnerRequiredTargets

@[expose] public section
/-! Covering every missing target rules out new ordinary spokes on the
protected set, even when prescribed matching endpoints consume some old
spokes. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem inner_complement_completion_no_new_spokes
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (I:Finset V) (J:Finset U) (X:U→Type) [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (Y Old End Outer Outside R Absorber Prescribed:U→Finset V)
    (B:∀u,Finset (X u)) (Φ g:∀u,X u→V)
    (hR:∀u,R u=Finset.univ\(Outside u∪End u))
    (hOldBound:∀u,Old u⊆Y u∪(Outside u∪End u))
    (hNewBound:∀u,Finset.univ.image (Φ u)⊆Y u∪(Outside u∪End u))
    (hAbs:∀u∈J,Disjoint (Absorber u) I)
    (hB:∀u,(B u).image (g u)=Prescribed u∪innerRequiredTargets J I Outer Y Absorber Old u)
    (hag:∀u x,x∈B u→Φ u x=g u x):
    ∀u∈J,∀v∈I,v∈R u\Y u→v∈Outer u :=by
  intro u hu v hvI hvR
  by_contra hnOuter
  have hRmem: v∈R u:=(Finset.mem_sdiff.mp hvR).1
  have hnY:v∉Y u:=(Finset.mem_sdiff.mp hvR).2
  have hnOutside:v∉Outside u ∧ v∉End u:=by
    rw [hR u] at hRmem
    have hn: v∉Outside u∪End u:=(Finset.mem_sdiff.mp hRmem).2
    exact ⟨fun h=>hn (Finset.mem_union_left _ h),fun h=>hn (Finset.mem_union_right _ h)⟩
  have hnOld:v∉Old u:=by
    intro ho
    rcases Finset.mem_union.mp (hOldBound u ho) with hy|h
    · exact hnY hy
    · rcases Finset.mem_union.mp h with ho|he
      · exact hnOutside.1 ho
      · exact hnOutside.2 he
  have hnAbs:v∉Absorber u:=by
    intro ha
    exact (Finset.disjoint_left.mp (hAbs u hu)) ha hvI
  have htarget:v∈innerRequiredTargets J I Outer Y Absorber Old u:=by
    simp only [innerRequiredTargets,hu,if_true,Finset.mem_sdiff,Finset.mem_union,not_or]
    exact ⟨hvI,⟨⟨⟨hnOuter,hnY⟩,hnAbs⟩,hnOld⟩⟩
  have hmem:v∈(B u).image (g u):=by
    rw [hB u]
    exact Finset.mem_union_right _ htarget
  obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hmem
  have himage:v∈Finset.univ.image (Φ u):=
    Finset.mem_image.mpr ⟨x,Finset.mem_univ _,(hag u x hx).trans hxv⟩
  rcases Finset.mem_union.mp (hNewBound u himage) with hy|h
  · exact hnY hy
  · rcases Finset.mem_union.mp h with ho|he
    · exact hnOutside.1 ho
    · exact hnOutside.2 he
end Oberwolfach
