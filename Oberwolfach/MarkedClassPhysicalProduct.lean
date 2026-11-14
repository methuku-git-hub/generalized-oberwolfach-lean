module

public import Oberwolfach.MarkedClassPhysicalRefinement

@[expose] public section
/-! One global edge-colour exposure and one shared orientation per edge
produce every marked class's expanded physical marginal simultaneously. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_prod_map_first {Ω Γ:Type} [Fintype Ω] [Fintype Γ]
    (μ:FiniteLaw Ω) (ν:FiniteLaw Γ):
    (μ.prod ν).map Prod.fst=μ:=by
  apply finiteLaw_ext
  intro x
  have hh:=finiteLaw_prod_first_probability μ ν (fun y=>y=x)
  have hm:=finiteLaw_map_probability (μ.prod ν) Prod.fst (fun y=>y=x)
  have hp:=hm.trans hh
  simpa [FiniteLaw.probability,eq_comm] using hp

theorem marked_class_physical_product {E:Type} [Fintype E] [DecidableEq E] {k:ℕ}
    (ρ p t p₂ t₂ u:Fin k→ℝ)
    (hρ:∀ a,0<ρ a) (htotal:∑ a,ρ a=1)
    (hp:∀ a,0≤p a) (ht:∀ a,0≤t a) (hp₂:∀ a,0≤p₂ a) (ht₂:∀ a,0≤t₂ a) (hu:∀ a,0≤u a)
    (hbalance:∀ a,2*p a+2*t a+2*p₂ a+2*t₂ a+u a=ρ a):
    let hρ0:=fun a=>(hρ a).le
    let inside:=fun a=>FiniteLaw.categorical (markedPhysicalInsideProbability (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a))
      (marked_physical_inside_nonneg (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a) (hρ a))
      (marked_physical_inside_sum (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hρ a) (hbalance a))
    let joint:=(FiniteLaw.categorical ρ hρ0 htotal).sigma inside
    let physical:=joint.prod FiniteLaw.fairCoin
    let law:=FiniteLaw.pi (fun _:E=>physical);
    law.map (fun z e=>(z e).1.1)=FiniteLaw.pi (fun _:E=>FiniteLaw.categorical ρ hρ0 htotal) ∧
    ∀ a,law.map (fun z e=>(markedPhysicalOptionIndex (classRefinedView a (z e).1),(z e).2))=
      FiniteLaw.pi (fun _:E=>FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability (p a) (t a) (p₂ a) (t₂ a) (u a))
        (markedExpandedPhysicalProbability_nonneg (p a) (t a) (p₂ a) (t₂ a) (u a)
          (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a)
          (by have hh:=Finset.single_le_sum (fun b _=>(hρ b).le) (Finset.mem_univ a);linarith [hbalance a]))
        (markedExpandedPhysicalProbability_sum (p a) (t a) (p₂ a) (t₂ a) (u a))):=by
  intro hρ0 inside joint physical law
  dsimp only [law]
  constructor
  · rw [finiteLaw_pi_map (fun _:E=>physical) (fun (_:E) z=>z.1.1)]
    congr 1
    funext i
    calc
      _ = (physical.map Prod.fst).map (fun z=>z.1):=by rw [finiteLaw_map_map]
      _ = joint.map (fun z=>z.1):=by rw [finiteLaw_prod_map_first]
      _ = _:=finiteLaw_sigma_map_first _ _
  · intro a
    rw [finiteLaw_pi_map (fun _:E=>physical) (fun (_:E) z=>(markedPhysicalOptionIndex (classRefinedView a z.1),z.2))]
    congr 1
    funext i
    exact marked_class_physical_refinement ρ p t p₂ t₂ u hρ htotal hp ht hp₂ ht₂ hu hbalance a
end Oberwolfach
