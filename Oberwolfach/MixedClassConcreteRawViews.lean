module

public import Oberwolfach.MarkedClassSharedOrdinaryLaw
public import Oberwolfach.MixedClassPhysicalView

@[expose] public section
/-! Each class may use its ordinary or expanded marked raw view of the same
categorical physical exposure and class-local interval variables. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_class_concrete_raw_views {V:Type} [Fintype V] [DecidableEq V] {k:ℕ}
    (marks:Fin k→Bool)
    (U:Fin k→Type) [∀ a,Fintype (U a)] [∀ a,DecidableEq (U a)]
    (ρ p t p₂ t₂ u:Fin k→ℝ)
    (hρ:∀ a,0<ρ a) (htotal:∑ a,ρ a=1)
    (hp:∀ a,0≤p a) (ht:∀ a,0≤t a) (hp₂:∀ a,0≤p₂ a) (ht₂:∀ a,0≤t₂ a) (hu:∀ a,0≤u a)
    (hbalance:∀ a,2*p a+2*t a+2*p₂ a+2*t₂ a+u a=ρ a)
    (d:Fin k→ℕ) (hd:∀ a,2≤d a)
    (q:∀ a,U a→Bool→ℝ) (hq:∀ a w g,0≤q a w g) (hQ:∀ a w,∑ g,q a w g≤1/8)
    (s:∀ a,U a→Bool→ℝ) (hs:∀ a w j,0≤s a w j)
    (hS:∀ a w,∑ j,s a w j ≤ intervalUncoveredProbability (d a) (∑ g,q a w g)):
    let hρ0:=fun a=>(hρ a).le
    let hρ1:=fun a=>show ρ a≤1 from by
      have hh:=Finset.single_le_sum (fun b _=>(hρ b).le) (Finset.mem_univ a);linarith
    let inside:=fun a=>FiniteLaw.categorical (markedPhysicalInsideProbability (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a))
      (marked_physical_inside_nonneg (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a) (hρ a))
      (marked_physical_inside_sum (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hρ a) (hbalance a))
    let joint:=(FiniteLaw.categorical ρ hρ0 htotal).sigma inside
    let physical:=FiniteLaw.pi (fun _:Sym2 V=>joint.prod FiniteLaw.fairCoin)
    let μ:=fun a=>rawExpandedMarkedWheelLaw (V:=V) (U:=U a) (p a) (t a) (p₂ a) (t₂ a) (u a)
      (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a) (by linarith [hbalance a,hρ1 a])
      (d a) (hd a) (q a) (hq a) (hQ a) (s a) (hs a) (hS a)
    let ν:=fun a=>rawWheelLaw (V:=V) (U:=U a) (fun _=>ρ a) (fun _=>hρ0 a) (fun _=>hρ1 a)
      (d a) (hd a) (q a) (hq a) (hQ a) (s a) (hs a) (hS a)
    let noise:=fun a=>FiniteLaw.pi (fun e=>μ a (Sum.inr e))
    let law:=physical.prod (FiniteLaw.pi noise);
    law.map (fun z e=>(z.1 e).1.1)=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categorical ρ hρ0 htotal) ∧
    ∀ a, law.map (mixedClassView (marks a)
      (fun z=>combineSumCoordinates (fun e=>(markedPhysicalOptionIndex (classRefinedView a (z.1 e).1),(z.1 e).2)) (z.2 a))
      (fun z=>combineSumCoordinates (S:=RawWheelCoordinateState Bool Bool)
        (fun e=>classColourMembership a (z.1 e).1.1) (z.2 a))) =
      mixedClassLaw (marks a) (FiniteLaw.pi (μ a)) (FiniteLaw.pi (ν a)) :=by
  intro hρ0 hρ1 inside joint physical μ ν noise law
  have h:=marked_class_shared_ordinary_law (V:=V) U ρ p t p₂ t₂ u hρ htotal hp ht hp₂ ht₂ hu hbalance d hd q hq hQ s hs hS
  constructor
  · simpa [law,noise,physical,inside,joint,μ] using h.1
  · intro a
    apply mixed_class_physical_view
    · simpa [law,noise,physical,inside,joint,μ] using h.2.1 a
    · simpa [law,noise,physical,inside,joint,μ,ν] using h.2.2 a
end Oberwolfach
