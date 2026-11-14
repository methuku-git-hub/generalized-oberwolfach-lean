module

public import Oberwolfach.OrdinaryActualCrossProfile
public import Oberwolfach.OrdinaryInnerCrossBalance

@[expose] public section
/-! The sampled fixed-domain event simultaneously supplies the actual
inner and boundary cross balance after a bounded edit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_same_sample_balance_profiles
    (P F Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (J:Finset U)
    (pR pH tR tH e L:ℝ) (htR:0≤tR) (htH:0≤tH) (he:0≤e) (hL:0≤L)
    (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hrows:RawOrdinaryRows P π d 2 I pR s j tR σ)
    (hcols:RawOrdinaryDomainIndices F π d 3 J pH j tH σ)
    (hparent:∀v,|pR*(P.neighborFinset v∩I).card-2*pH*J.card|≤e)
    (hrim:∀v,((changed (Q.neighborFinset v) ((rawWheelGraph P σ).neighborFinset v)).card:ℝ)≤L)
    (hspoke:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)≤L):
    let b:=e+tR+2*tH+3*L;
    (∀v,|((Q.neighborFinset v∩I).card:ℝ)-2*(J.filter (H v)).card|≤b) ∧
    (∀v,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b):=by
  intro b
  have hc:=ordinary_actual_cross_balance_from_sample P F Q H π d I J pR pH tR tH e L s j σ
    hrows hcols hparent hrim hspoke
  refine ⟨hc,?_⟩
  have hb:0≤b:=by dsimp [b];positivity
  exact ordinary_inner_balance_from_cross_profile Q H I J b hb (fun v _=>hc v)
end Oberwolfach
