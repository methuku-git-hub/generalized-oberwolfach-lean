module

public import Oberwolfach.ClassSharedRawProduct
public import Oberwolfach.MarkedExpandedRawLaw

@[expose] public section
/-! All marked classes may use one global physical colouring and one shared
orientation while retaining their exact separate raw wheel laws. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_class_shared_raw_law {V:Type} [Fintype V] [DecidableEq V] {k:ℕ}
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
    let inside:=fun a=>FiniteLaw.categorical (markedPhysicalInsideProbability (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a))
      (marked_physical_inside_nonneg (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a) (hρ a))
      (marked_physical_inside_sum (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hρ a) (hbalance a))
    let joint:=(FiniteLaw.categorical ρ hρ0 htotal).sigma inside
    let physical:=FiniteLaw.pi (fun _:Sym2 V=>joint.prod FiniteLaw.fairCoin)
    let μ:=fun a=>rawExpandedMarkedWheelLaw (V:=V) (U:=U a) (p a) (t a) (p₂ a) (t₂ a) (u a)
      (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a)
      (by have hh:=Finset.single_le_sum (fun b _=>(hρ b).le) (Finset.mem_univ a);linarith [hbalance a])
      (d a) (hd a) (q a) (hq a) (hQ a) (s a) (hs a) (hS a)
    let noise:=fun a=>FiniteLaw.pi (fun e=>μ a (Sum.inr e))
    let law:=physical.prod (FiniteLaw.pi noise);
    law.map (fun z e=>(z.1 e).1.1)=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categorical ρ hρ0 htotal) ∧
    ∀ a,law.map (fun z=>combineSumCoordinates
      (fun e=>(markedPhysicalOptionIndex (classRefinedView a (z.1 e).1),(z.1 e).2)) (z.2 a))=
        FiniteLaw.pi (μ a):=by
  intro hρ0 inside joint physical μ noise law
  have hphysical:=marked_class_physical_product (E:=Sym2 V) ρ p t p₂ t₂ u hρ htotal hp ht hp₂ ht₂ hu hbalance
  let view:=fun (a:Fin k) (z:Sym2 V→((Σ _:Fin k,Fin 5)×Bool)) e=>(markedPhysicalOptionIndex (classRefinedView a (z e).1),(z e).2)
  have hview:∀ a,physical.map (view a)=FiniteLaw.pi (fun e=>μ a (Sum.inl e)):=by
    intro a
    exact hphysical.2 a
  have h:=class_shared_raw_product physical (fun z e=>(z e).1.1) view μ hview
  exact ⟨by simpa [physical] using h.1.trans hphysical.1,h.2⟩
end Oberwolfach
