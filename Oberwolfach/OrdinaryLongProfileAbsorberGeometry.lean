module

public import Oberwolfach.OrdinarySampledProfileProperty

@[expose] public section
/-! Two-neighbourhood consequences of the sampled pair-profile inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U] {r:ℕ}
theorem ordinary_long_profile_absorber_geometry
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (pmin smin:ℝ) (j:Color) (β η a b:ℝ) [Nonempty U]
    (h:ordinarySampledProfileProperty (r:=r) P F π d σ pmin smin j β η a b):
    let Q:=rawWheelGraph P σ\F;
    let H:=rawWheelSpokes π d σ j;
    (∀ v w,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w).card:ℝ)) ∧
    (∀ u u' v w,β*Fintype.card V≤(((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ)) := by
  intro Q H
  have hpair: ∀ u u' v w,β*Fintype.card V≤(((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ) := by
    intro u u' v w
    have hh:=h.1 u u' v w
    convert hh using 1
    congr 1
    congr 1
    ext z
    simp [Q,H]
  refine ⟨?_,hpair⟩
  intro v w
  let u:U:=Classical.choice inferInstance
  apply le_trans (hpair u u v w)
  have hsub : ((Finset.univ.filter (fun a=>H a u∧H a u))∩Q.neighborFinset v∩Q.neighborFinset w) ⊆ Q.neighborFinset v∩Q.neighborFinset w := by
    intro a ha
    simp only [Finset.mem_inter] at ha ⊢
    exact ⟨ha.1.2,ha.2⟩
  exact_mod_cast Finset.card_le_card hsub
end Oberwolfach
