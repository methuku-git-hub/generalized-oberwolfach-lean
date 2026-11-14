module

public import Oberwolfach.OrdinarySpokePotentialIdentity
public import Oberwolfach.ResourcePatternIndicatorSum

@[expose] public section
/-! The omitted-spoke test written as a predicate on an ordinary wheel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U] {r:ℕ}

theorem ordinary_spoke_pattern_predicate (P Q F:SimpleGraph V) (H:V→U→Prop)
    (v:V) (u:U) (W:OrdinaryWheel P F (fun _ :V=>fun _ :U=>True) r):
    (Sum.inr (v,u)∈ordinaryWheelResources W ∧
      ∀ e∈ordinaryWheelResources W\{Sum.inr (v,u)},ordinaryResourceState Q H e=true) ↔
      ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support ∧ ordinaryWheelRim W≤Q ∧
        (∀ z∈(ordinaryWheelRim W).support,z≠v→H z u) := by
  constructor
  · intro hh
    have hs:ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support :=
      (ordinaryWheelResources_spoke W v u).mp hh.1
    have ht:ordinaryWheelRim W≤Q ∧ ∀ z∈(ordinaryWheelRim W).support,z≠v→H z u:=
      (ordinary_spoke_omitted_resources W Q H v u hs.1).mp hh.2
    exact ⟨hs.1,hs.2,ht.1,ht.2⟩
  · rintro ⟨hu,hv,hq,hh⟩
    exact ⟨(ordinaryWheelResources_spoke W v u).mpr ⟨hu,hv⟩,
      (ordinary_spoke_omitted_resources W Q H v u hu).mpr ⟨hq,hh⟩⟩
end Oberwolfach
