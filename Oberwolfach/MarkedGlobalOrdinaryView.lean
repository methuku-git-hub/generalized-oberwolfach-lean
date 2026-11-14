module

public import Oberwolfach.MarkedClassPhysicalProduct
public import Oberwolfach.ClassColourBernoulli

@[expose] public section
/-! The same global physical experiment also gives each ordinary class its
independent-edge membership sample. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_global_ordinary_view {E:Type} [Fintype E] [DecidableEq E] {k:ℕ}
    (ρ p t p₂ t₂ u:Fin k→ℝ)
    (hρ:∀ a,0<ρ a) (htotal:∑ a,ρ a=1)
    (hp:∀ a,0≤p a) (ht:∀ a,0≤t a) (hp₂:∀ a,0≤p₂ a) (ht₂:∀ a,0≤t₂ a) (hu:∀ a,0≤u a)
    (hbalance:∀ a,2*p a+2*t a+2*p₂ a+2*t₂ a+u a=ρ a):
    let hρ0:=fun a=>(hρ a).le
    let inside:=fun a=>FiniteLaw.categorical (markedPhysicalInsideProbability (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a))
      (marked_physical_inside_nonneg (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a) (hρ a))
      (marked_physical_inside_sum (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hρ a) (hbalance a))
    let joint:=(FiniteLaw.categorical ρ hρ0 htotal).sigma inside
    let physical:=FiniteLaw.pi (fun _:E=>joint.prod FiniteLaw.fairCoin);
    ∀ a,physical.map (fun z e=>classColourMembership a (z e).1.1)=
      FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin (ρ a) (hρ a).le
        (by have hh:=Finset.single_le_sum (fun b _=>(hρ b).le) (Finset.mem_univ a);linarith)):=by
  intro hρ0 inside joint physical a
  have hphys:physical.map (fun z e=>(z e).1.1)=FiniteLaw.pi (fun _:E=>FiniteLaw.categorical ρ hρ0 htotal):=
    (marked_class_physical_product ρ p t p₂ t₂ u hρ htotal hp ht hp₂ ht₂ hu hbalance).1
  calc
    _ = (physical.map (fun z e=>(z e).1.1)).map (fun c e=>classColourMembership a (c e)):=by rw [finiteLaw_map_map]
    _ = _:=by rw [hphys];exact categorical_class_membership_product ρ hρ0 htotal a
end Oberwolfach
