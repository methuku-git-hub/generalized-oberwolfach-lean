module

public import Oberwolfach.MixedClassConcreteRawViews
public import Oberwolfach.ClassRetainedSimultaneousEvents

@[expose] public section
/-! Common categorical exposure, class-specific retention, and a common
event for a bounded mixture of ordinary and marked classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_class_concrete_retained_common_event (K:ℕ):
    ∃ χ:ℝ,0<χ ∧ ∃ N:ℕ,∀ k:ℕ,k≤K+1→
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (marks:Fin k→Bool)
    (U:Fin k→Type) [∀ a,Fintype (U a)] [∀ a,DecidableEq (U a)]
    (ρ p t p₂ t₂ u:Fin k→ℝ)
    (hρ:∀ a,0<ρ a) (htotal:∑ a,ρ a=1)
    (hp:∀ a,0≤p a) (ht:∀ a,0≤t a) (hp₂:∀ a,0≤p₂ a) (ht₂:∀ a,0≤t₂ a) (hu:∀ a,0≤u a)
    (hbalance:∀ a,2*p a+2*t a+2*p₂ a+2*t₂ a+u a=ρ a)
    (d:Fin k→ℕ) (hd:∀ a,2≤d a)
    (q:∀ a,U a→Bool→ℝ) (hq:∀ a w g,0≤q a w g) (hQ:∀ a w,∑ g,q a w g≤1/8)
    (s:∀ a,U a→Bool→ℝ) (hs:∀ a w j,0≤s a w j)
    (hS:∀ a w,∑ j,s a w j ≤ intervalUncoveredProbability (d a) (∑ g,q a w g)),
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
    let law:=physical.prod (FiniteLaw.pi noise)

    let A:=fun a=>mixedClassState (marks a)
      (∀ e:RawWheelCoordinate V (U a),RawExpandedMarkedCoordinateState Bool Bool e)
      (RawWheelOutcome V (U a) Bool Bool)
    let raw:=fun a=>mixedClassLaw (marks a) (FiniteLaw.pi (μ a)) (FiniteLaw.pi (ν a))
    let view:=fun a=>mixedClassView (marks a)
      (fun z=>combineSumCoordinates (fun e=>(markedPhysicalOptionIndex (classRefinedView a (z.1 e).1),(z.1 e).2)) (z.2 a))
      (fun z=>combineSumCoordinates (S:=RawWheelCoordinateState Bool Bool)
        (fun e=>classColourMembership a (z.1 e).1.1) (z.2 a));
    ∀ (F:∀ a,A a→Type) [∀ a x,Fintype (F a x)] (τ:∀ a x,FiniteLaw (F a x))
      (Partition:(Sym2 V→Fin k)→Prop) (Good:∀ a,(Σ x:A a,F a x)→Prop),
    1-1/(Fintype.card V:ℝ)^10≤(FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categorical ρ hρ0 htotal)).probability Partition→
    (∀ a,1-(100*χ+200/(Fintype.card V:ℝ))≤((raw a).sigma (τ a)).probability (Good a))→
    let total:=law.sigma (fun z=>FiniteLaw.pi (fun a=>τ a (view a z)));
    ∃ z,0<total.mass z ∧ Partition (fun e=>(z.1.1 e).1.1) ∧ ∀ a,Good a ⟨view a z.1,z.2 a⟩:=by
  obtain ⟨χ,hχ,N,hN⟩:=class_retained_simultaneous_events_200 K
  refine ⟨χ,hχ,N,?_⟩
  intro k hk V _ _ hn marks U _ _ ρ p t p₂ t₂ u hρ htotal hp ht hp₂ ht₂ hu hbalance d hd q hq hQ s hs hS
    hρ0 hρ1 inside joint physical μ ν noise law A raw view F _ τ Partition Good hpart hgood total
  have hc:=mixed_class_concrete_raw_views (V:=V) marks U ρ p t p₂ t₂ u hρ htotal hp ht hp₂ ht₂ hu hbalance d hd q hq hQ s hs hS
  have hcolour:law.map (fun z e=>(z.1 e).1.1)=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categorical ρ hρ0 htotal):=by
    simpa [law,noise,physical,joint,inside,μ] using hc.1
  have hview:∀ a,law.map (view a)=raw a:=by
    intro a
    simpa [view,raw,law,noise,physical,joint,inside,μ,ν,A] using hc.2 a
  letI : ∀ a,Fintype (A a) := by
    intro a
    dsimp [A]
    infer_instance
  exact hN k (Fintype.card V) hk hn _ _ A F law (fun z e=>(z.1 e).1.1)
    (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categorical ρ hρ0 htotal)) view raw hcolour hview τ Partition Good hpart hgood
end Oberwolfach
