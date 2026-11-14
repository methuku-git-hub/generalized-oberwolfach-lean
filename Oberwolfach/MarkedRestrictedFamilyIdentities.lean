module

public import Oberwolfach.MarkedFamilyRestrictionLift

@[expose] public section

/-! Restriction and lifting leave the actual row sets, hubs, physical rim
graph and spoke relation unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T I : Type} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U]
    {tail head : E→V} {ktail khead : T→V} {H₀ HK H₀' HK' : V→U→Prop}
    {π : Equiv.Perm V} {m b : ℕ}

theorem marked_restricted_family_rim
    (PE : E→Prop) (PT : T→Prop)
    (hH₀ : ∀ x u,H₀' x u→H₀ x u) (hHK : ∀ x u,HK' x u→HK x u)
    (C : I→MarkedWheel (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PT e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' HK') :
    markedFamilyRim (fun i=>markedWheelToLarger PE PT hH₀ hHK (C i))=markedFamilyRim C := by
  apply iSup_congr
  intro i
  unfold markedWheelRimGraph
  rw [show (markedWheelToLarger PE PT hH₀ hHK (C i)).1=markedCycleToLarger PE PT (C i).1 from rfl,
    markedCycleToLarger_physical]

theorem marked_restricted_family_spokes
    (PE : E→Prop) (PT : T→Prop)
    (hH₀ : ∀ x u,H₀' x u→H₀ x u) (hHK : ∀ x u,HK' x u→HK x u)
    (C : I→MarkedWheel (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PT e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' HK') :
    markedFamilySpokes (fun i=>markedWheelToLarger PE PT hH₀ hHK (C i))=markedFamilySpokes C := rfl

theorem marked_restricted_wheel_avoids_deletions (D : SimpleGraph V) (J : V→U→Prop)
    (C : MarkedWheel
      (fun e:{e:E//¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:T//¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val)
      m π b (fun x u=>H₀ x u∧¬J x u) (fun x u=>HK x u∧¬J x u)) :
    Disjoint (markedWheelRimGraph C) D ∧
    ∀ x u,Sum.inr (x,u)∈markedWheelPhysicalResources C→¬J x u := by
  constructor
  · apply disjoint_iff_inf_le.mpr
    intro x y hxy
    exact (marked_cycle_rim_avoids_deleted_graph D C.1 x y hxy.1.2 hxy.2).elim
  · intro x u hu
    rcases markedWheelPhysicalResources_spoke_present C x u hu with h|h <;> exact h.2

end Oberwolfach
