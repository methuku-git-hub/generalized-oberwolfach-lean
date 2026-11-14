module

public import Oberwolfach.MarkedReservationComplement

@[expose] public section

/-! A packing in the actual reservation complement uses no physical
resource lying wholly inside the protected row and hub sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_complement_packing_avoids_inner (m b:ℕ) (X:Finset V) (Z:Finset U)
    (hX:∀ x,π x∈X↔x∈X) (σ:Sym2 (V⊕U)→Bool)
    (M:Finset (MarkedWheel
      (fun e:{e:E//¬markedBoundaryRimAllowed π X σ false (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K//¬markedBoundaryRimAllowed π X σ true (ktail e) (khead e)}=>ktail e.val) (fun e=>khead e.val)
      m π b (fun x u=>H₀ x u∧¬markedBoundarySpokeAllowed X Z σ x u)
        (fun x u=>HK x u∧¬markedBoundarySpokeAllowed X Z σ x u))):
    ∀ e∈M.biUnion markedWheelPhysicalResources,¬markedInnerResource X Z e:=by
  intro e he hinner
  obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
  cases e with
  | inl e=>
    rw [markedWheelPhysicalResources_rim] at he
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp he
    simp only [Function.comp_apply] at hi
    generalize markedCycleTypedEdge _ _ _ _ m π b W.1 i=a at hi
    cases a with
    | inl a=>
      change ({tail a.val,head a.val}:Finset V)=e at hi
      change e⊆X at hinner
      rw [←hi,Finset.insert_subset_iff,Finset.singleton_subset_iff] at hinner
      exact a.property (Or.inl hinner)
    | inr a=>
      change ({ktail a.val,π (khead a.val)}:Finset V)=e at hi
      change e⊆X at hinner
      rw [←hi,Finset.insert_subset_iff,Finset.singleton_subset_iff,hX] at hinner
      exact a.property (Or.inl hinner)
  | inr z=>
    have hs:=markedWheelPhysicalResources_spoke_present W z.1 z.2 he
    have ha:markedBoundarySpokeAllowed X Z σ z.1 z.2:=Or.inl hinner
    exact hs.elim (fun h=>h.2 ha) (fun h=>h.2 ha)
end Oberwolfach
