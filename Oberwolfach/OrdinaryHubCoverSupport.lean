module

public import Oberwolfach.HubCoverByIncidence
public import Oberwolfach.RowCoverPackings

@[expose] public section

/-! Support and degree consequences of the exact hub-cover resource identity.
Every wheel uses a prescribed hub; its rim vertices belong to that hub's
specified neighbourhood. These conclusions will isolate the free vertices
when the subsequent row-root covers are chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r n:ℕ}

theorem ordinary_hub_packing_spokes (M:Finset (OrdinaryWheel Q F H r))
    (u:Fin n→U) (T:Fin n→Finset V)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))))
    (v:V) (a:U):
    ordinaryPackingSpokes M v a ↔ ∃ i,a=u i ∧ v∈T i:=by
  have he:ordinaryPackingSpokes M v a ↔ Sum.inr (v,a)∈M.biUnion ordinaryWheelResources:=by
    simp only [ordinaryPackingSpokes,Finset.mem_biUnion,ordinaryWheelResources_spoke]
  rw [he,hunion]
  simp only [Finset.mem_union,Finset.mem_image,Sum.inl_ne_inr,and_false,exists_false,
    false_or,Finset.mem_biUnion,Finset.mem_univ,true_and,Sum.inr.injEq,Prod.mk.injEq]
  constructor
  · rintro ⟨i,w,hw,rfl,ha⟩
    exact ⟨i,ha.symm,hw⟩
  · rintro ⟨i,rfl,hi⟩
    exact ⟨i,v,hi,rfl,rfl⟩

theorem ordinary_hub_packing_wheel_support (M:Finset (OrdinaryWheel Q F H r))
    (hr:0<r) (u:Fin n→U) (hu:Function.Injective u) (T:Fin n→Finset V)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))))
    (W:OrdinaryWheel Q F H r) (hW:W∈M):
    ∃ i,ordinaryWheelHub W=u i ∧ ∀ v∈(ordinaryWheelRim W).support,v∈T i:=by
  have hc:(ordinaryWheelRim W).support.toFinset.card=r:=W.val.1.val.property.support_card
  obtain ⟨v,hv⟩:=Finset.card_pos.mp (hc.symm ▸ hr)
  have hv':v∈(ordinaryWheelRim W).support:=by simpa only [Set.mem_toFinset] using hv
  obtain ⟨i,hi,hvi⟩:=(ordinary_hub_packing_spokes M u T hunion v (ordinaryWheelHub W)).mp ⟨W,hW,rfl,hv'⟩
  refine ⟨i,hi,?_⟩
  intro z hz
  obtain ⟨j,hj,hzj⟩:=(ordinary_hub_packing_spokes M u T hunion z (ordinaryWheelHub W)).mp ⟨W,hW,rfl,hz⟩
  have hji:j=i:=hu (hj.symm.trans hi)
  simpa only [hji] using hzj

theorem ordinary_hub_packing_row_degree (M:Finset (OrdinaryWheel Q F H r))
    (u:Fin n→U) (T:Fin n→Finset V)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))))
    (v:V):
    (Finset.univ.filter (ordinaryPackingSpokes M v)).card≤n:=by
  have hs:Finset.univ.filter (ordinaryPackingSpokes M v)⊆Finset.univ.image u:=by
    intro a ha
    obtain ⟨i,hi,_⟩:=(ordinary_hub_packing_spokes M u T hunion v a).mp (Finset.mem_filter.mp ha).2
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans (by simp))

end Oberwolfach
