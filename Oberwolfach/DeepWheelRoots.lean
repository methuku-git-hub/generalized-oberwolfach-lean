module

public import Oberwolfach.HubRowPackingSupport

@[expose] public section

/-! The physical vertex set of an ordinary wheel includes its rim vertices
in the first summand and its hub in the second. The deep cover has exactly
one prescribed root per wheel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r nh nr:ℕ}

def ordinaryWheelVertices (W:OrdinaryWheel Q F H r):Finset (V⊕U):=
  (ordinaryWheelRim W).support.toFinset.image Sum.inl∪{Sum.inr (ordinaryWheelHub W)}

theorem ordinaryWheelVertices_rim (W:OrdinaryWheel Q F H r) (v:V):
    Sum.inl v∈ordinaryWheelVertices W↔v∈(ordinaryWheelRim W).support:=by
  simp only [ordinaryWheelVertices,Finset.mem_union,Finset.mem_image,Set.mem_toFinset,
    Finset.mem_singleton,Sum.inl_ne_inr,or_false,Sum.inl.injEq,exists_eq_right]

theorem ordinaryWheelVertices_hub (W:OrdinaryWheel Q F H r) (a:U):
    Sum.inr a∈ordinaryWheelVertices W↔a=ordinaryWheelHub W:=by
  simp only [ordinaryWheelVertices,Finset.mem_union,Finset.mem_image,Sum.inl_ne_inr,and_false,
    exists_false,false_or,Finset.mem_singleton,Sum.inr.injEq]

theorem ordinary_deep_wheel_unique_root (W:OrdinaryWheel Q F H r)
    (I:Finset V) (J:Finset U) (u:Fin nh→U) (x:Fin nr→V)
    (hu:∀ i,u i∈J) (hx:∀ i,x i∈I)
    (hsupport:
      (∃ i,ordinaryWheelHub W=u i ∧ ∀ v∈(ordinaryWheelRim W).support,v∉I) ∨
      (∃ i,x i∈(ordinaryWheelRim W).support ∧ ordinaryWheelHub W∉J ∧
        ∀ v∈(ordinaryWheelRim W).support,v=x i∨v∉I)):
    (ordinaryWheelVertices W∩((Finset.univ.image (fun i=>Sum.inl (x i)))∪
      (Finset.univ.image (fun i=>Sum.inr (u i))))).card=1:=by
  let Roots:Finset (V⊕U):=Finset.univ.image (fun i=>Sum.inl (x i))∪Finset.univ.image (fun i=>Sum.inr (u i))
  have hR (v:V):Sum.inl v∈Roots↔∃ i,x i=v:=by
    simp only [Roots,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,
      Sum.inl.injEq,Sum.inr_ne_inl,exists_false,or_false]
  have hU (a:U):Sum.inr a∈Roots↔∃ i,u i=a:=by
    simp only [Roots,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,
      Sum.inr.injEq,Sum.inl_ne_inr,exists_false,false_or]
  change (ordinaryWheelVertices W∩Roots).card=1
  rcases hsupport with ⟨i,hi,hs⟩|⟨i,hxi,hi,hs⟩
  · have he:ordinaryWheelVertices W∩Roots={Sum.inr (u i)}:=by
      ext z
      cases z with
      | inl v=>
        simp only [Finset.mem_inter,ordinaryWheelVertices_rim,hR,Finset.mem_singleton,Sum.inl_ne_inr,iff_false,not_and]
        intro hv hroot
        obtain ⟨k,rfl⟩:=hroot
        exact hs (x k) hv (hx k)
      | inr a=>
        simp only [Finset.mem_inter,ordinaryWheelVertices_hub,hU,Finset.mem_singleton,Sum.inr.injEq,hi]
        constructor
        · exact fun h=>h.1
        · intro ha;exact ⟨ha,⟨i,ha.symm⟩⟩
    rw [he,Finset.card_singleton]
  · have he:ordinaryWheelVertices W∩Roots={Sum.inl (x i)}:=by
      ext z
      cases z with
      | inl v=>
        simp only [Finset.mem_inter,ordinaryWheelVertices_rim,hR,Finset.mem_singleton,Sum.inl.injEq]
        constructor
        · rintro ⟨hv,k,hk⟩
          exact (hs v hv).resolve_right (fun h=>h (hk ▸ hx k))
        · rintro rfl;exact ⟨hxi,i,rfl⟩
      | inr a=>
        simp only [Finset.mem_inter,ordinaryWheelVertices_hub,hU,Finset.mem_singleton,Sum.inr_ne_inl,iff_false,not_and]
        intro ha hroot
        obtain ⟨k,hk⟩:=hroot
        exact hi (ha ▸ hk ▸ hu k)
    rw [he,Finset.card_singleton]

end Oberwolfach
