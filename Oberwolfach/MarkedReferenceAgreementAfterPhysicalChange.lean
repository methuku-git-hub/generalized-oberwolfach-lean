module

public import Oberwolfach.MarkedModifiedPhysicalIncidence
public import Oberwolfach.MarkedReferenceInputStability

@[expose] public section
/-! Original interval coordinates and the same physical spoke-change graph
control both ambient row and hub agreement after an arbitrary host change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_spoke_reference_agreement_after_physical_change
    (π:Equiv.Perm V) (d:ℕ) (σ τ:RawMarkedOutcome V U Γ Color) (g:Γ) (j:Color)
    (H H':Bool→V→U→Prop) (FS:SimpleGraph (V⊕U)) (eR eC δ:ℝ)
    (hinterval:∀ e,σ (Sum.inr e)=τ (Sum.inr e))
    (hchange:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hrow:∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤eR)
    (hcol:∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤eC)
    (hFS:∀ z,(FS.degree z:ℝ)≤δ):
    (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d τ g j b x u↔H' b x u) then (1:ℝ) else 0)≤eR+δ) ∧
    (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d τ g j b x u↔H' b x u) then (1:ℝ) else 0)≤eC+δ) :=by
  have hi:(fun e=>σ (Sum.inr e))=(fun e=>τ (Sum.inr e)):=funext hinterval
  have hs:rawMarkedPairSpokes π d σ g j=rawMarkedPairSpokes π d τ g j:=by
    unfold rawMarkedPairSpokes
    rw [hi]
  have tri (a b c:Prop):(if ¬(a↔c) then (1:ℝ) else 0)≤
      (if ¬(a↔b) then (1:ℝ) else 0)+(if ¬(b↔c) then (1:ℝ) else 0):=by
    by_cases ha:a <;> by_cases hb:b <;> by_cases hc:c <;> simp [ha,hb,hc]
  obtain ⟨hR,hC⟩:=marked_spoke_physical_change_incidence H H' FS hchange
  constructor
  · intro b x
    have hchange':(∑ u,if ¬(H b x u↔H' b x u) then (1:ℝ) else 0)≤δ:=by
      have hh:=(hR b x).trans (hFS (Sum.inl x))
      convert hh using 1
      apply Finset.sum_congr rfl
      intro u _
      unfold bipAdj
      split_ifs <;> simp_all
    calc
      _ ≤ (∑ u,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)+
          (∑ u,if ¬(H b x u↔H' b x u) then (1:ℝ) else 0):=by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro u _
        rw [←hs]
        exact tri (rawMarkedPairSpokes π d σ g j b x u) (H b x u) (H' b x u)
      _ ≤ eR+δ:=add_le_add (hrow b x) hchange'
  · intro b u
    have hchange':(∑ x,if ¬(H b x u↔H' b x u) then (1:ℝ) else 0)≤δ:=by
      have hh:=(hC b u).trans (hFS (Sum.inr u))
      convert hh using 1
      apply Finset.sum_congr rfl
      intro x _
      unfold bipAdj
      split_ifs <;> simp_all
    calc
      _ ≤ (∑ x,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)+
          (∑ x,if ¬(H b x u↔H' b x u) then (1:ℝ) else 0):=by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro x _
        rw [←hs]
        exact tri (rawMarkedPairSpokes π d σ g j b x u) (H b x u) (H' b x u)
      _ ≤ eC+δ:=add_le_add (hcol b u) hchange'
end Oberwolfach
