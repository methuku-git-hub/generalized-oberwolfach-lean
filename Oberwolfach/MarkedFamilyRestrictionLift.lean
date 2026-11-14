module

public import Oberwolfach.MarkedWheelFamilyLoads
public import Oberwolfach.MarkedPackingRimGraphs

@[expose] public section

/-! Lift wheels chosen after a previous physical wheel family has been
deleted. Their actual physical resources remain disjoint from that family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

theorem marked_family_restriction_lift (hm:1≤m) (hb:1≤b) (C:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (B:MarkedWheel
      (fun e:{e:E // ¬(markedFamilyRim C).Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // ¬(markedFamilyRim C).Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val)
      m π b (fun x u=>H₀ x u∧¬markedFamilySpokes C x u) (fun x u=>HK x u∧¬markedFamilySpokes C x u)):
    ∃ W:MarkedWheel tail head ktail khead m π b H₀ HK,
      W.1.val=B.1.val∧W.2.val=B.2.val∧markedWheelPhysicalResources W=markedWheelPhysicalResources B∧
      ∀ i,Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources W):=by
  let PE:=fun e:E=>¬(markedFamilyRim C).Adj (tail e) (head e)
  let PK:=fun e:K=>¬(markedFamilyRim C).Adj (ktail e) (π (khead e))
  let W:=markedWheelToLarger PE PK (fun _ _ h=>h.1) (fun _ _ h=>h.1) B
  have he:markedWheelPhysicalResources W=markedWheelPhysicalResources B:=markedWheelToLarger_resources _ _ _ _ _
  refine ⟨W,rfl,rfl,he,?_⟩
  intro i
  apply Finset.disjoint_left.mpr
  intro z hz hw
  rw [he] at hw
  cases z with
  | inl z=>
    rw [markedWheelPhysicalResources_rim] at hz hw
    have hc:z.card=2:=by
      obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hz
      rw [←ha]
      exact markedCycle_physical_edge_card tail head ktail khead m π b hm hb (C i).1 a
    obtain ⟨x,y,hxy,rfl⟩:=Finset.card_eq_two.mp hc
    exact marked_cycle_rim_avoids_deleted_graph (markedFamilyRim C) B.1 x y hw
      (SimpleGraph.iSup_adj.mpr ⟨i,hxy,hz⟩)
  | inr p=>
    have hh:=markedWheelPhysicalResources_spoke_present B p.1 p.2 hw
    have hs:¬markedFamilySpokes C p.1 p.2:=by rcases hh with h|h <;> exact h.2
    rw [markedWheelPhysicalResources_spoke] at hz
    exact hs ⟨i,hz.1,hz.2⟩

end Oberwolfach
