module

public import Oberwolfach.BipartiteNormalizedCutDeletion
public import Oberwolfach.OccurrenceRestrictionCuts
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! Restrict the two correction cut matrices away from the protected inner
rectangle, retaining the original orientation and an explicit cut margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_correction_cut_inputs
    (hn:0<Fintype.card V) (hu:0<Fintype.card U)
    (Q:SimpleGraph V) (H:V→U→Prop) (R:V→V→Prop) (T:Finset V) (B:Finset U) (δ h ζ:ℝ)
    (hζ:0≤ζ) (hζh:ζ≤h) (hT:(T.card:ℝ)≤ζ*Fintype.card V) (hB:(B.card:ℝ)≤ζ*Fintype.card U)
    (hOrient:∀x y,relationMultiplicity R x y+relationMultiplicity R y x=if Q.Adj x y then 1 else 0)
    (hcutR:BipartiteLargeCut (relationMultiplicity R) δ (2*h))
    (hcutH:BipartiteLargeCut (relationMultiplicity H) δ (2*h)):
    let FQ:=spanningRestriction Q T
    let FH:=fun v u=>v∈T ∧ u∈B
    let R':=fun x y=>R x y ∧ ¬(x∈T ∧ y∈T);
    (∀x y,relationMultiplicity R' x y+relationMultiplicity R' y x=if (Q\FQ).Adj x y then 1 else 0) ∧
    BipartiteLargeCut (relationMultiplicity R') δ h ∧
    BipartiteLargeCut (relationMultiplicity (fun v u=>H v u ∧ ¬FH v u)) δ h:=by
  intro FQ FH R'
  have hcR:=bipartiteLargeCut_delete_rectangle hn hn R T T δ (2*h) ζ hζ hT hT hcutR
  have hcH:=bipartiteLargeCut_delete_rectangle hn hu H T B δ (2*h) ζ hζ hT hB hcutH
  refine ⟨?_,bipartiteLargeCut_coefficient_mono _ δ (2*h-ζ) h (by linarith) hcR,
    bipartiteLargeCut_coefficient_mono _ δ (2*h-ζ) h (by linarith) hcH⟩
  intro x y
  have ho:=hOrient x y
  by_cases hx:x∈T <;> by_cases hy:y∈T <;>
    simp [R',FQ,relationMultiplicity,spanningRestriction_adj,hx,hy] at ho ⊢ <;> exact ho
end Oberwolfach
