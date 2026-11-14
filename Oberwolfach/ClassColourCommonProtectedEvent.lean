module

public import Oberwolfach.ClassColourBernoulli
public import Oberwolfach.FiniteHighEventsCommon
public import Oberwolfach.TwoCommonEvents
public import Oberwolfach.CoordinateLocalLemma

@[expose] public section
/-! Join the class preparation events to a global protected-partition event
on the same categorical colouring, without assuming independence between
classes or between the preparation and partition events. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem categorical_class_events_with_global_event
    {E:Type} [Fintype E] [DecidableEq E] {k:ℕ}
    (ρ:Fin k→ℝ) (hρ:∀a,0≤ρ a) (htotal:∑a,ρ a=1)
    (ClassEvent:Fin k→(E→Bool)→Prop) (GlobalEvent:(E→Fin k)→Prop)
    (err:Fin k→ℝ) (globalErr:ℝ)
    (hClass:∀a,1-err a≤
      (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin (ρ a) (hρ a)
        (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith))).probability (ClassEvent a))
    (hGlobal:1-globalErr≤
      (FiniteLaw.pi (fun _:E=>FiniteLaw.categorical ρ hρ htotal)).probability GlobalEvent):
    let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.categorical ρ hρ htotal);
    1-globalErr-(∑a,err a)≤μ.probability
      (fun c=>GlobalEvent c ∧ ∀a,ClassEvent a (fun e=>classColourMembership a (c e))) :=by
  let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.categorical ρ hρ htotal)
  have hEach:∀a:Fin k,1-err a≤μ.probability
      (fun c=>ClassEvent a (fun e=>classColourMembership a (c e))):=by
    intro a
    have hmap:=finiteLaw_map_probability μ (fun c e=>classColourMembership a (c e)) (ClassEvent a)
    rw [categorical_class_membership_product ρ hρ htotal a] at hmap
    rw [←hmap]
    exact hClass a
  have hAll:1-(∑a,err a)≤μ.probability
      (fun c=>∀a,ClassEvent a (fun e=>classColourMembership a (c e))):=by
    have h:=finiteLaw_high_events_common μ Finset.univ
      (fun a c=>ClassEvent a (fun e=>classColourMembership a (c e))) err
      (by intro a ha;exact hEach a)
    simpa only [Finset.mem_univ, true_implies] using h
  exact finiteLaw_two_events_lower μ GlobalEvent
    (fun c=>∀a,ClassEvent a (fun e=>classColourMembership a (c e))) globalErr (∑a,err a) hGlobal hAll

theorem categorical_class_events_with_global_witness
    {E:Type} [Fintype E] [DecidableEq E] {k:ℕ}
    (ρ:Fin k→ℝ) (hρ:∀a,0≤ρ a) (htotal:∑a,ρ a=1)
    (ClassEvent:Fin k→(E→Bool)→Prop) (GlobalEvent:(E→Fin k)→Prop)
    (err:Fin k→ℝ) (globalErr:ℝ)
    (hClass:∀a,1-err a≤
      (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin (ρ a) (hρ a)
        (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith))).probability (ClassEvent a))
    (hGlobal:1-globalErr≤
      (FiniteLaw.pi (fun _:E=>FiniteLaw.categorical ρ hρ htotal)).probability GlobalEvent)
    (hbudget:globalErr+(∑a,err a)<1):
    ∃c:E→Fin k,GlobalEvent c ∧ ∀a,ClassEvent a (fun e=>classColourMembership a (c e)) :=by
  let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.categorical ρ hρ htotal)
  have h:=categorical_class_events_with_global_event ρ hρ htotal ClassEvent GlobalEvent err globalErr hClass hGlobal
  have hp:0<μ.probability (fun c=>GlobalEvent c ∧ ∀a,ClassEvent a (fun e=>classColourMembership a (c e))):=by
    apply lt_of_lt_of_le _ h
    linarith
  obtain ⟨c,_,hc⟩:=finiteLaw_positive_event_exists μ _ hp
  exact ⟨c,hc⟩
end Oberwolfach
