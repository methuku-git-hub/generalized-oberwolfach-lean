module

public import Oberwolfach.OrdinaryHubCoverSupport
public import Oberwolfach.Neighbourhoods

@[expose] public section

/-! Removing a hub cover leaves every later row-root star unchanged when
its rim vertices lie in the free set. Spokes in the fixed later hub domain
are unchanged, even though columns at the already covered hubs can be large. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r n:ℕ}

theorem ordinary_hub_cover_avoids_other_rows (M:Finset (OrdinaryWheel Q F H r))
    (hr:0<r) (u:Fin n→U) (hu:Function.Injective u) (T:Fin n→Finset V)
    (X:Finset V) (hX:∀ i,T i⊆X)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i)))):
    (∀ v,v∉X→∀ w,¬(ordinaryWheelRimGraph M).Adj v w) ∧
    (∀ v,v∉X→∀ a,¬ordinaryPackingSpokes M v a):=by
  constructor
  · intro v hv w hvw
    obtain ⟨W,hW,hh⟩:=(ordinaryWheelRimGraph_edges M s(v,w)).mp hvw
    obtain ⟨i,_,hi⟩:=ordinary_hub_packing_wheel_support M hr u hu T hunion W hW
    exact hv (hX i (hi v hh.mem_support_left))
  · intro v hv a hh
    obtain ⟨i,_,hi⟩:=(ordinary_hub_packing_spokes M u T hunion v a).mp hh
    exact hv (hX i hi)

theorem ordinary_hub_deletion_preserves_row_balance (M:Finset (OrdinaryWheel Q F H r))
    (hr:0<r) (u:Fin n→U) (hu:Function.Injective u) (T:Fin n→Finset V)
    (X:Finset V) (hX:∀ i,T i⊆X)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))))
    (v:V) (hv:v∉X):
    (Q\ordinaryWheelRimGraph M).neighborFinset v=Q.neighborFinset v ∧
    (Finset.univ.filter (fun a=>H v a∧¬ordinaryPackingSpokes M v a))=Finset.univ.filter (H v):=by
  obtain ⟨hrim,hspoke⟩:=ordinary_hub_cover_avoids_other_rows M hr u hu T X hX hunion
  constructor
  · ext w
    simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj,hrim v hv w,not_false_eq_true,and_true]
  · ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hspoke v hv a,not_false_eq_true,and_true]

theorem ordinary_hub_deletion_fixed_domain (M:Finset (OrdinaryWheel Q F H r))
    (u:Fin n→U) (T:Fin n→Finset V) (A:Finset V) (B:Finset U) (hB:∀ i,u i∉B)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))))
    (hdeg:∀ v,(ordinaryWheelRimGraph M).degree v≤2*n):
    (∀ v,(changed (A∩Q.neighborFinset v) (A∩(Q\ordinaryWheelRimGraph M).neighborFinset v)).card≤2*n) ∧
    (∀ v,B∩Finset.univ.filter (fun a=>H v a∧¬ordinaryPackingSpokes M v a)=B∩Finset.univ.filter (H v)) ∧
    (∀ a∈B,A∩Finset.univ.filter (fun v=>H v a∧¬ordinaryPackingSpokes M v a)=A∩Finset.univ.filter (fun v=>H v a)):=by
  have hno (v:V) (a:U) (ha:a∈B):¬ordinaryPackingSpokes M v a:=by
    intro hh
    obtain ⟨i,rfl,_⟩:=(ordinary_hub_packing_spokes M u T hunion v a).mp hh
    exact hB i ha
  refine ⟨?_,?_,?_⟩
  · intro v
    have hs:changed (A∩Q.neighborFinset v) (A∩(Q\ordinaryWheelRimGraph M).neighborFinset v)⊆
        (ordinaryWheelRimGraph M).neighborFinset v:=by
      intro w hw
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,
        SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj] at hw ⊢
      tauto
    exact (Finset.card_le_card hs).trans (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg v)
  · intro v
    ext a
    simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨ha,hva,_⟩;exact ⟨ha,hva⟩
    · rintro ⟨ha,hva⟩;exact ⟨ha,hva,hno v a ha⟩
  · intro a ha
    ext v
    simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,hno v a ha,not_false_eq_true,and_true]

theorem ordinary_wheel_avoids_removed_packing (M:Finset (OrdinaryWheel Q F H r))
    (W:OrdinaryWheel (Q\ordinaryWheelRimGraph M) F
      (fun v a=>H v a∧¬ordinaryPackingSpokes M v a) r):
    Disjoint (ordinaryWheelResources W) (M.biUnion ordinaryWheelResources):=by
  apply Finset.disjoint_left.mpr
  intro e he heM
  obtain ⟨Z,hZ,heZ⟩:=Finset.mem_biUnion.mp heM
  cases e with
  | inl e=>
    have hw:=(ordinaryWheelResources_rim W e).mp he
    have hz:=(ordinaryWheelResources_rim Z e).mp heZ
    have hD:(ordinaryWheelRimGraph M).edgeSet e:=
      (ordinaryWheelRimGraph_edges M e).mpr ⟨Z,hZ,hz⟩
    have hQ:=SimpleGraph.edgeSet_mono W.val.1.property hw
    have hsd:(Q\ordinaryWheelRimGraph M).edgeSet=Q.edgeSet\(ordinaryWheelRimGraph M).edgeSet:=by
      ext a
      induction a using Sym2.inductionOn with
      | _ v w=>simp only [SimpleGraph.mem_edgeSet,SimpleGraph.sdiff_adj,Set.mem_sdiff]
    rw [hsd] at hQ
    exact hQ.2 hD
  | inr va=>
    obtain ⟨hW,hw⟩:=(ordinaryWheelResources_spoke W va.1 va.2).mp he
    obtain ⟨hZhub,hz⟩:=(ordinaryWheelResources_spoke Z va.1 va.2).mp heZ
    exact (W.property.1 va.1 hw).2 ⟨Z,hZ,hZhub.trans hW.symm,hz⟩

theorem changed_card_triangle {T:Type*} (A B C:Finset T):
    (changed A C).card≤(changed A B).card+(changed B C).card:=by
  classical
  have hs:changed A C⊆changed A B∪changed B C:=by
    intro x hx
    simp only [changed,Finset.mem_union,Finset.mem_sdiff] at hx ⊢
    tauto
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

end Oberwolfach
