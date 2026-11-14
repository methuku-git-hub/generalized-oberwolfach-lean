module

public import Oberwolfach.ResidualDirectedDegreeBalance

@[expose] public section
/-! An oriented partial embedding has exactly one incident arc at each
label in its tail or head image. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem injective_image_incidence_card
    {E A V:Type*} [Fintype E] [DecidableEq A] [DecidableEq V]
    (f:E→A) (g:A→V) (hinj:Function.Injective (g∘f)) (v:V):
    ((Finset.univ.image f).filter (fun e=>g e=v)).card=
      if v∈Finset.univ.image (g∘f) then 1 else 0:=by
  classical
  by_cases hv:v∈Finset.univ.image (g∘f)
  · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hv
    have heq:(Finset.univ.image f).filter (fun e=>g e=v)={f i}:=by
      ext e
      simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · rintro ⟨⟨j,hj⟩,hgj⟩
        rw [←hj] at hgj
        have hji:j=i:=hinj (by simpa only [Function.comp_apply] using hgj.trans hi.symm)
        simpa only [hji] using hj.symm
      · intro he
        subst e
        exact ⟨⟨i,rfl⟩,hi⟩
    rw [heq]
    simp [hv]
  · have heq:(Finset.univ.image f).filter (fun e=>g e=v)=∅:=by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨⟨i,_,rfl⟩,hi⟩:=Finset.mem_filter.mp he |>.imp_left Finset.mem_image.mp
      exact hv (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)
    rw [heq]
    simp [hv]

theorem oriented_partial_embedding_incidence
    {E V:Type*} [Fintype E] [DecidableEq V]
    (tail head:E↪V) (v:V):
    let D:Finset (V×V):=Finset.univ.image (fun e=>(tail e,head e))
    (D.filter (fun e=>e.1=v)).card=(if v∈Finset.univ.image tail then 1 else 0) ∧
    (D.filter (fun e=>e.2=v)).card=(if v∈Finset.univ.image head then 1 else 0):=by
  constructor
  · simpa only [Function.comp_def] using
      injective_image_incidence_card (fun e:E=>(tail e,head e)) Prod.fst tail.injective v
  · simpa only [Function.comp_def] using
      injective_image_incidence_card (fun e:E=>(tail e,head e)) Prod.snd head.injective v
end Oberwolfach
