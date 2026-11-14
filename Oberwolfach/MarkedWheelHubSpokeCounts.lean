module

public import Oberwolfach.TypedMarkedPotentialResources

@[expose] public section
/-! Each marked wheel has exactly one marked spoke at its own hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

def markedHubSpokeRoots (u:U):Finset ((E⊕K)⊕(Bool×V×U)):=
  Finset.univ.image (fun v:V=>Sum.inr (true,v,u))

theorem marked_wheel_hub_marked_spoke_count
    (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ) (u:U):
    (typedMarkedOccurrenceResources W∩markedHubSpokeRoots (V:=V) (E:=E) (K:=K) u).card=
      if W.2.val=u then 1 else 0 := by
  by_cases he:W.2.val=u
  · have hset : typedMarkedOccurrenceResources W∩markedHubSpokeRoots (V:=V) (E:=E) (K:=K) u =
        {Sum.inr (true,W.1.val 0,u)} := by
      ext a
      cases a with
      | inl e=>simp [markedHubSpokeRoots]
      | inr z=>
        rcases z with ⟨c,v,t⟩
        simp only [Finset.mem_inter,typedMarkedOccurrenceResources_spoke,markedHubSpokeRoots,
          Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton,Sum.inr.injEq,Prod.mk.injEq]
        constructor
        · rintro ⟨⟨i,hb,hv,ht⟩,⟨x,hc,hx,hu⟩⟩
          have hi:i=0:=by simpa [←hc] using hb
          subst i
          exact ⟨hc.symm,hv.symm,hu.symm⟩
        · rintro ⟨hc,hv,ht⟩
          subst c
          refine ⟨⟨0,by simp,hv.symm,?_⟩,⟨v,rfl,rfl,?_⟩⟩
          · exact he.trans ht.symm
          · exact ht.symm
    rw [hset]
    simp [he]
  · have hset : typedMarkedOccurrenceResources W∩markedHubSpokeRoots (V:=V) (E:=E) (K:=K) u=∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      have ha₁: a∈typedMarkedOccurrenceResources W:=(Finset.mem_inter.mp ha).1
      have ha₂: a∈markedHubSpokeRoots (V:=V) (E:=E) (K:=K) u:=(Finset.mem_inter.mp ha).2
      obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp ha₂
      obtain ⟨i,hi⟩:=(typedMarkedOccurrenceResources_spoke W (true,v,u)).mp ha₁
      exact he (congrArg (fun z:Bool×V×U=>z.2.2) hi)
    simp [hset,he]
end Oberwolfach
