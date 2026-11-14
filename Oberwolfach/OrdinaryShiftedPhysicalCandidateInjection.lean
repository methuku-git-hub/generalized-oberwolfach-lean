module

public import Oberwolfach.OrdinaryMixedPhysicalResourceFiber
public import Oberwolfach.RawMarkedCandidateGeometry

@[expose] public section
/-! A shifted wheel itself has distinct physical resources even though the
physical map is not injective across the full typed candidate universe. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem ordinary_shifted_candidate_physical_injective
    (hm:2≤m) (hb:1≤b)
    (W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b H₀ Hₖ):
    Set.InjOn (ordinaryMixedPhysicalResource (U:=U) π) (↑(typedMarkedOccurrenceResources W):Set (((V×V)⊕(V×V))⊕(Bool×V×U))) := by
  intro a ha z hz h
  cases a with
  | inl a=>
    cases z with
    | inl z=>
      obtain ⟨i,hi⟩:=(typedMarkedOccurrenceResources_rim W a).mp ha
      obtain ⟨j,hj⟩:=(typedMarkedOccurrenceResources_rim W z).mp hz
      have hp:markedPairPhysical π a=markedPairPhysical π z:=by
        simpa only [ordinaryMixedPhysicalResource,Sum.elim_inl,Sum.inl.injEq] using h
      have hij:i=j:=markedPairCycle_physical_injective hm hb W.1 (by
        simpa only [Function.comp_apply,hi,hj] using hp)
      exact congrArg Sum.inl (hi.symm.trans (hij ▸ hj))
    | inr z=>simp [ordinaryMixedPhysicalResource] at h
  | inr a=>
    cases z with
    | inl z=>simp [ordinaryMixedPhysicalResource] at h
    | inr z=>
      obtain ⟨i,hi⟩:=(typedMarkedOccurrenceResources_spoke W a).mp ha
      obtain ⟨j,hj⟩:=(typedMarkedOccurrenceResources_spoke W z).mp hz
      have hp:a.2=z.2:=by simpa only [ordinaryMixedPhysicalResource,Sum.elim_inr,Sum.inr.injEq] using h
      have hv:W.1.val i=W.1.val j:=by
        have hi':W.1.val i=a.2.1:=congrArg (fun q:Bool×V×U=>q.2.1) hi
        have hj':W.1.val j=z.2.1:=congrArg (fun q:Bool×V×U=>q.2.1) hj
        exact hi'.trans ((congrArg Prod.fst hp).trans hj'.symm)
      have hij:i=j:=permutationSeparated_injective π b W.1.val W.1.property.1 hv
      exact congrArg Sum.inr (hi.symm.trans (hij ▸ hj))
end Oberwolfach
