module

public import Oberwolfach.MarkedPhysicalConditionalLaw
public import Oberwolfach.FiniteLawProductMap
public import Oberwolfach.FiniteLawComposition

@[expose] public section
/-! A single shared class and orientation, followed by the manuscript's
conditional marked physical state, has the exact expanded physical law for
every individual class. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_class_physical_refinement {k:ℕ}
    (ρ p t p₂ t₂ u:Fin k→ℝ)
    (hρ:∀ a,0<ρ a) (htotal:∑ a,ρ a=1)
    (hp:∀ a,0≤p a) (ht:∀ a,0≤t a) (hp₂:∀ a,0≤p₂ a) (ht₂:∀ a,0≤t₂ a) (hu:∀ a,0≤u a)
    (hbalance:∀ a,2*p a+2*t a+2*p₂ a+2*t₂ a+u a=ρ a):
    let hρ0:=fun a=>(hρ a).le
    let inside:=fun a=>FiniteLaw.categorical (markedPhysicalInsideProbability (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a))
      (marked_physical_inside_nonneg (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a) (hρ a))
      (marked_physical_inside_sum (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a) (hρ a) (hbalance a))
    let joint:=(FiniteLaw.categorical ρ hρ0 htotal).sigma inside
    let physical:=joint.prod FiniteLaw.fairCoin;
    ∀ a,
      physical.map (fun z=>(markedPhysicalOptionIndex (classRefinedView a z.1),z.2))=
      FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability (p a) (t a) (p₂ a) (t₂ a) (u a))
        (markedExpandedPhysicalProbability_nonneg (p a) (t a) (p₂ a) (t₂ a) (u a)
          (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a)
          (by have hh:=Finset.single_le_sum (fun b _=>(hρ b).le) (Finset.mem_univ a);linarith [hbalance a]))
        (markedExpandedPhysicalProbability_sum (p a) (t a) (p₂ a) (t₂ a) (u a)):=by
  intro hρ0 inside joint physical a
  have hρ1:ρ a≤1:=by
    have hh:=Finset.single_le_sum (fun b _=>(hρ b).le) (Finset.mem_univ a)
    linarith
  have hbase:joint.map (classRefinedView (A:=Fin 5) a)=FiniteLaw.optional (ρ a) (hρ a).le hρ1 (inside a):=by
    exact categorical_refinement_class_marginal ρ hρ0 htotal inside a
  have hopt: (FiniteLaw.optional (ρ a) (hρ a).le hρ1 (inside a)).map markedPhysicalOptionIndex=
      FiniteLaw.categorical (markedExpandedPhysicalProbability (p a) (t a) (p₂ a) (t₂ a) (u a))
        (markedExpandedPhysicalProbability_nonneg (p a) (t a) (p₂ a) (t₂ a) (u a)
          (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a) (by linarith [hbalance a]))
        (markedExpandedPhysicalProbability_sum (p a) (t a) (p₂ a) (t₂ a) (u a)):=
    marked_physical_option_refinement (p a) (t a) (p₂ a) (t₂ a) (u a) (ρ a)
      (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a) (hρ a) hρ1 (hbalance a)
  calc
    _ = (physical.map (fun z=>(classRefinedView a z.1,z.2))).map
      (fun z=>(markedPhysicalOptionIndex z.1,z.2)):=by rw [finiteLaw_map_map]
    _ = ((joint.map (classRefinedView a)).prod FiniteLaw.fairCoin).map
      (fun z=>(markedPhysicalOptionIndex z.1,z.2)):=by rw [finiteLaw_prod_map_left]
    _ = ((FiniteLaw.optional (ρ a) (hρ a).le hρ1 (inside a)).prod FiniteLaw.fairCoin).map
      (fun z=>(markedPhysicalOptionIndex z.1,z.2)):=by rw [hbase]
    _ = ((FiniteLaw.optional (ρ a) (hρ a).le hρ1 (inside a)).map markedPhysicalOptionIndex).prod FiniteLaw.fairCoin:=
      finiteLaw_prod_map_left _ _ _
    _ = (FiniteLaw.categorical (markedExpandedPhysicalProbability (p a) (t a) (p₂ a) (t₂ a) (u a))
        (markedExpandedPhysicalProbability_nonneg (p a) (t a) (p₂ a) (t₂ a) (u a)
          (hp a) (ht a) (hp₂ a) (ht₂ a) (hu a) (by linarith [hbalance a]))
        (markedExpandedPhysicalProbability_sum (p a) (t a) (p₂ a) (t₂ a) (u a))).prod FiniteLaw.fairCoin:=by rw [hopt]
    _ = _:= (finiteLaw_categorical_direction_prod _ _ _).symm
end Oberwolfach
