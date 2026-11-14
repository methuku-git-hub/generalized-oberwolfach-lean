module

public import Oberwolfach.MarkedReferenceWeightedLoadAfterChanges

@[expose] public section
/-! The normalized physical-change budget for the same fixed potential weights. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_weighted_load_scaled_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _=>True) (fun _ _=>True)→ℝ) (B ζ:ℝ) (hB:0≤B) (hζ:0≤ζ)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hdegR:∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V)
    (hdegS:∀ x,(DS.degree x:ℝ)≤ζ*Fintype.card V)
    (hrim:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈DR.edgeFinset)
    (hspoke:∀ b x u,¬(H b x u↔H' b x u)→DS.Adj (Sum.inl x) (Sum.inr u))
    (valid:(((V×V)⊕(V×V))⊕(Bool×V×U))→Prop) (error target:ℝ)
    (hbase:∀ root,valid root→
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ) H root-1|≤error)
    (hbudget:error+33*((m:ℝ)+1)^4*B*ζ≤target):
    ∀ root,valid root→
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d τ) H' root-1|≤target := by
  have hpos:0≤ζ*(Fintype.card V:ℝ):=mul_nonneg hζ (Nat.cast_nonneg _)
  have hn0:(Fintype.card V:ℝ)≠0:=by exact_mod_cast (ne_of_gt hn)
  have hbound:=marked_reference_weighted_load_after_changes P π d m hm hn hu σ τ H H' w B hB hw DR DS
    (ζ*Fintype.card V) (ζ*Fintype.card V) hpos hpos hdegR
    (fun x=>hdegS (Sum.inl x)) (fun u=>hdegS (Sum.inr u)) hrim hspoke valid error hbase
  intro root hroot
  have heq: error+11*((m:ℝ)+1)^4*B*(2*(ζ*Fintype.card V)+ζ*Fintype.card V)/Fintype.card V =
    error+33*((m:ℝ)+1)^4*B*ζ:=by field_simp; ring
  rw [heq] at hbound
  exact (hbound root hroot).trans hbudget
end Oberwolfach
