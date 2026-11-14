module

public import Oberwolfach.MarkedFiniteBalanceEmbedding

@[expose] public section

/-! Restrict typed occurrences and both spoke types while retaining the
same ambient roots. This is the exact numerical counterpart of the
subtype representation of a deleted or domain-restricted host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteBalance_subtype_restriction
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (PE:E→Prop) (PK:K→Prop) (P:V→U→Prop) (m:ℕ) (z:V⊕U) (i:Fin 4):
    markedFiniteBalance (fun a:{e:E//PE e}=>tail a.val) (fun a:{e:E//PE e}=>head a.val)
      (fun a:{e:K//PK e}=>ktail a.val) (fun a:{e:K//PK e}=>khead a.val)
      (fun x u=>HK x u∧P x u) Finset.univ
      (Finset.univ.filter (fun s:V×U=>(H₀ s.1 s.2∧P s.1 s.2)∨(HK s.1 s.2∧P s.1 s.2))) m z i=
    markedFiniteBalance tail head ktail khead HK
      (Finset.univ.filter (Sum.elim PE PK))
      ((Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).filter (fun s=>P s.1 s.2)) m z i:=by
  let e:{a:E//PE a}↪E:=⟨Subtype.val,Subtype.val_injective⟩
  let k:{a:K//PK a}↪K:=⟨Subtype.val,Subtype.val_injective⟩
  let S:=Finset.univ.filter (fun s:V×U=>(H₀ s.1 s.2∧P s.1 s.2)∨(HK s.1 s.2∧P s.1 s.2))
  have hAr:Finset.univ.image (e.sumMap k)=Finset.univ.filter (Sum.elim PE PK):=by
    ext a
    cases a with
    | inl a=>
      simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_filter,Sum.elim_inl]
      constructor
      · rintro ⟨b,hb⟩
        cases b with
        | inl b=>have h:b.val=a:=Sum.inl.inj hb;exact h ▸ b.property
        | inr b=>exact (Sum.inr_ne_inl hb).elim
      · intro ha;exact ⟨Sum.inl ⟨a,ha⟩,rfl⟩
    | inr a=>
      simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_filter,Sum.elim_inr]
      constructor
      · rintro ⟨b,hb⟩
        cases b with
        | inl b=>exact (Sum.inl_ne_inr hb).elim
        | inr b=>have h:b.val=a:=Sum.inr.inj hb;exact h ▸ b.property
      · intro ha;exact ⟨Sum.inr ⟨a,ha⟩,rfl⟩
  have hS:S.image (Prod.map (Function.Embedding.refl V) (Function.Embedding.refl U))=
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).filter (fun s=>P s.1 s.2):=by
    have hh:Prod.map (Function.Embedding.refl V) (Function.Embedding.refl U)=id:=rfl
    rw [hh,Finset.image_id]
    ext s;simp only [S,Finset.mem_filter,Finset.mem_univ,true_and];tauto
  have hz:Sum.map (Function.Embedding.refl V) (Function.Embedding.refl U) z=z:=by cases z <;> rfl
  have h:=markedFiniteBalance_embedding
    (fun a:{e:E//PE e}=>tail a.val) (fun a:{e:E//PE e}=>head a.val)
    (fun a:{e:K//PK e}=>ktail a.val) (fun a:{e:K//PK e}=>khead a.val)
    tail head ktail khead (fun x u=>HK x u∧P x u) HK
    (Function.Embedding.refl V) (Function.Embedding.refl U) e k
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) Finset.univ S m
    (by
      intro s hs
      have hp:P s.1 s.2:=((Finset.mem_filter.mp hs).2).elim And.right And.right
      exact (and_iff_left hp).symm) z i
  rw [hAr,hS,hz] at h
  exact h.symm

end Oberwolfach
