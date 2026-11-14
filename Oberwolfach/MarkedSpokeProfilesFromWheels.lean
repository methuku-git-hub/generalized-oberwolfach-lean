module

public import Oberwolfach.MarkedSpokeHubRootProfiles
public import Oberwolfach.MarkedRawSpokeTypes

@[expose] public section

/-! Recover all free-path spoke types from the constructed wheels and then
supply the exact root classes to the common-profile hub-switch theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 11000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K S:Type} [Fintype S] [Fintype U] [DecidableEq S] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_root_order_free_spokes (m:ℕ)
    (C:MarkedWheel tail head ktail khead m π b H₀ HK) (v:V) (p:Fin m→V) (j:Bool)
    (hC:∀ i,C.1.val i=rootedCycleOrder (markedRootOrder m j) v p i):
    ∀ k:Fin m,if rootFirstSpokeType m j k.succ then HK (p k) C.2.val else H₀ (p k) C.2.val:=by
  intro k
  have h:=(markedHubCompatible_iff_positions H₀ HK C.1.val C.2.val).mp C.2.property
    ((markedRootOrder m j).symm k.succ)
  simpa only [markedRootOrder_position_type,hC,rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_succ] using h

theorem marked_spoke_profiles_from_wheels (m:ℕ) (hm:3≤m)
    (p:S→(Fin m↪V)) (j:S→Bool) (v v':S→V) (hub:S→U) (ψ:U→U)
    (C D:S→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hC:∀ s i,(C s).1.val i=rootedCycleOrder (markedRootOrder m (j s)) (v s) (p s) i)
    (hD:∀ s i,(D s).1.val i=rootedCycleOrder (markedRootOrder m (j s)) (v' s) (p s) i)
    (hCh:∀ s,(C s).2.val=hub s) (hDh:∀ s,(D s).2.val=ψ (hub s))
    (hdis:∀ s t,s≠t→Disjoint (Finset.univ.image (p s)) (Finset.univ.image (p t)))
    (hbal:∀ u,(Finset.univ.filter (fun s:{s:S // hub s=u}=>j s.val=false)).card=
      m*(Finset.univ.filter (fun s:{s:S // hub s=u}=>j s.val=true)).card)
    (htypes:∀ v u,HK v u→¬H₀ v u):
    ∃ ZK ZO:U→Finset V,∀ u,
      ZK u∪ZO u=spokePathHubVertices m p hub u∧Disjoint (ZK u) (ZO u)∧
      (ZO u).card=m*(ZK u).card∧(ZK u).card≤Fintype.card S∧
      (spokePathHubVertices m p hub u).card=m*Fintype.card {s:S // hub s=u}∧
      (∀ x∈ZK u,HK x u∧HK x (ψ u))∧
      (∀ x∈ZO u,H₀ x u∧H₀ x (ψ u)):=by
  have hsp:∀ s k,if rootFirstSpokeType m (j s) k.succ then
      HK (p s k) (hub s)∧HK (p s k) (ψ (hub s)) else
      H₀ (p s k) (hub s)∧H₀ (p s k) (ψ (hub s)):=by
    intro s k
    have hc:=marked_root_order_free_spokes m (C s) (v s) (p s) (j s) (hC s) k
    have hd:=marked_root_order_free_spokes m (D s) (v' s) (p s) (j s) (hD s) k
    rw [hCh] at hc
    rw [hDh] at hd
    cases hj:rootFirstSpokeType m (j s) k.succ <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at hc hd ⊢
    all_goals exact ⟨hc,hd⟩
  obtain ⟨ZK,ZO,hZ⟩:=marked_spoke_hub_root_profiles m hm p j hub ψ hdis hbal H₀ HK htypes hsp
  refine ⟨ZK,ZO,?_⟩
  intro u
  obtain ⟨hunion,hdis,hcard,hKcard,hsize,hK,hO⟩:=hZ u
  refine ⟨hunion,hdis,hcard,?_,hsize,?_,?_⟩
  · rw [hKcard]
    exact (Finset.card_le_univ _).trans (Fintype.card_subtype_le _)
  · intro x hx
    apply (hK x ?_).mp hx
    rw [←hunion]
    exact Finset.mem_union_left _ hx
  · intro x hx
    apply (hO x ?_).mp hx
    rw [←hunion]
    exact Finset.mem_union_right _ hx

end Oberwolfach
