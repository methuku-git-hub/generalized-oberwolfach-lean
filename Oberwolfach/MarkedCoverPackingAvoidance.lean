module

public import Oberwolfach.MarkedCoverRetainedHost
public import Oberwolfach.MarkedInnerResources
public import Oberwolfach.MarkedRowCoverRestrictionLift

@[expose] public section

/-! The earlier approximate packing can have large global degrees.
Avoidance instead uses its exclusion from the inner pair and retained
boundary, and the exact prescribed outside intersection of the new packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem marked_cover_resource_outside_if_forbidden
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (m b:ℕ) (X:Finset V) (Z:Finset U) (hX:∀ x,π x∈X↔x∈X)
    (σ:Sym2 (V⊕U)→Bool) (B:Finset (Finset V⊕(V×U)))
    (hr:∀ j x y,markedBoundaryRimAllowed π X σ j x y→
      Sum.inl (if j then ({x,π y}:Finset V) else {x,y})∉B)
    (hs:∀ x u,markedBoundarySpokeAllowed X Z σ x u→Sum.inr (x,u)∉B)
    (W:MarkedWheel
      (fun e:{e:E//markedCoverRimAllowed π X σ false (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K//markedCoverRimAllowed π X σ true (ktail e) (khead e)}=>ktail e.val) (fun e=>khead e.val)
      m π b (fun x u=>H₀ x u∧markedCoverSpokeAllowed X Z σ x u)
        (fun x u=>HK x u∧markedCoverSpokeAllowed X Z σ x u))
    (e:Finset V⊕(V×U)) (he:e∈markedWheelPhysicalResources W) (hB:e∈B):
    markedInnerResource (Xᶜ) (Zᶜ) e:=by
  cases e with
  | inl e=>
    rw [markedWheelPhysicalResources_rim] at he
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp he
    simp only [Function.comp_apply] at hi
    generalize markedCycleTypedEdge _ _ _ _ m π b W.1 i=a at hi
    cases a with
    | inl a=>
      change ({tail a.val,head a.val}:Finset V)=e at hi
      rw [←hi] at hB ⊢
      rcases a.property with ho|hb
      · change ({tail a.val,head a.val}:Finset V)⊆Xᶜ
        simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_compl] using ho
      · exact (hr false _ _ hb hB).elim
    | inr a=>
      change ({ktail a.val,π (khead a.val)}:Finset V)=e at hi
      rw [←hi] at hB ⊢
      rcases a.property with ho|hb
      · change ({ktail a.val,π (khead a.val)}:Finset V)⊆Xᶜ
        simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_compl,hX] using ho
      · exact (hr true _ _ hb hB).elim
  | inr e=>
    have hh:=markedWheelPhysicalResources_spoke_present W e.1 e.2 he
    have ha:markedCoverSpokeAllowed X Z σ e.1 e.2:=hh.elim (fun h=>h.2) (fun h=>h.2)
    rcases ha with ho|hb
    · exact ⟨Finset.mem_compl.mpr ho.1,Finset.mem_compl.mpr ho.2⟩
    · exact (hs _ _ hb hB).elim

theorem marked_cover_packing_avoids_earlier
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (m b:ℕ) (X:Finset V) (Z:Finset U) (hX:∀ x,π x∈X↔x∈X)
    (σ:Sym2 (V⊕U)→Bool) (B required:Finset (Finset V⊕(V×U)))
    (hr:∀ j x y,markedBoundaryRimAllowed π X σ j x y→
      Sum.inl (if j then ({x,π y}:Finset V) else {x,y})∉B)
    (hs:∀ x u,markedBoundarySpokeAllowed X Z σ x u→Sum.inr (x,u)∉B)
    (hreq:Disjoint required B)
    (M:Finset (MarkedWheel
      (fun e:{e:E//markedCoverRimAllowed π X σ false (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K//markedCoverRimAllowed π X σ true (ktail e) (khead e)}=>ktail e.val) (fun e=>khead e.val)
      m π b (fun x u=>H₀ x u∧markedCoverSpokeAllowed X Z σ x u)
        (fun x u=>HK x u∧markedCoverSpokeAllowed X Z σ x u)))
    (hM:(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) (Zᶜ))=required):
    Disjoint (M.biUnion markedWheelPhysicalResources) B:=by
  apply Finset.disjoint_left.mpr
  intro e he hB
  obtain ⟨W,hW,heW⟩:=Finset.mem_biUnion.mp he
  have hout:=marked_cover_resource_outside_if_forbidden tail head ktail khead H₀ HK π m b X Z hX σ B hr hs W e heW hB
  have h: e∈required:=by rw [←hM];exact Finset.mem_filter.mpr ⟨he,hout⟩
  exact Finset.disjoint_left.mp hreq h hB
end Oberwolfach
