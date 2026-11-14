module

public import Oberwolfach.OrderedOrdinaryWheelResources

@[expose] public section
/-! A wheel based at a hub uses exactly one spoke at each of its rim
vertices, and no spoke based at another hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {r b:ℕ} {π:Equiv.Perm V}

def ordinaryHubSpokeRoots (u:U):Finset ((V×V)⊕(V×U)):=
  Finset.univ.image (fun v:V=>Sum.inr (v,u))

theorem ordered_ordinary_hub_spoke_count
    (W:OrderedOrdinaryWheel (U:=U) π b r) (u:U):
    (orderedOrdinaryResources W∩ordinaryHubSpokeRoots (V:=V) u).card=
      if W.2=u then r else 0 := by
  by_cases he:W.2=u
  · have hset : orderedOrdinaryResources W∩ordinaryHubSpokeRoots (V:=V) u =
        Finset.univ.image (fun i:Fin r=>Sum.inr (W.1.val i,u)) := by
      ext a
      cases a with
      | inl xy=>simp [ordinaryHubSpokeRoots]
      | inr vu=>
        rcases vu with ⟨v,t⟩
        simp only [Finset.mem_inter,orderedOrdinaryResources_spoke,ordinaryHubSpokeRoots,
          Finset.mem_image,Finset.mem_univ,true_and,Sum.inr.injEq,Prod.mk.injEq]
        constructor
        · rintro ⟨⟨i,hi⟩,⟨a,ha⟩⟩
          refine ⟨i,?_⟩
          rcases hi with ⟨hiv,hit⟩
          rcases ha with ⟨_,hat⟩
          exact ⟨hiv,hat⟩
        · rintro ⟨i,hiv,hit⟩
          refine ⟨⟨i,hiv,?_⟩,⟨v,rfl,?_⟩⟩
          · exact he.trans hit
          · exact hit
    rw [hset,Finset.card_image_of_injective]
    · simp [he]
    · intro i j hij
      apply (permutationSeparated_injective π b W.1.val W.1.property)
      exact congrArg Prod.fst (Sum.inr.inj hij)
  · have hset : orderedOrdinaryResources W∩ordinaryHubSpokeRoots (V:=V) u=∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      have ha₁: a∈orderedOrdinaryResources W:=(Finset.mem_inter.mp ha).1
      have ha₂: a∈ordinaryHubSpokeRoots (V:=V) u:=(Finset.mem_inter.mp ha).2
      obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp ha₂
      obtain ⟨i,hi⟩:=(orderedOrdinaryResources_spoke W (v,u)).mp ha₁
      exact he (congrArg Prod.snd hi)
    simp [hset,he]
end Oberwolfach
