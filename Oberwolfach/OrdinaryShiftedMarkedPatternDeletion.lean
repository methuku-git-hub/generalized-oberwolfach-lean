module

public import Oberwolfach.OrdinaryShiftedMarkedDeletionStability
public import Oberwolfach.TypedMarkedPotentialDegreeStability

@[expose] public section
/-! Deleting bounded-degree physical rim edges changes every marked-wheel
root load by a controlled amount, with the seed weights fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_marked_pattern_deletion_stability
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (σ:RawMarkedOutcome V U Γ Color) (g:Γ) (j:Color)
    (D:SimpleGraph V) (δ:ℝ) (hδ:0≤δ) (hD:∀x,(D.degree x:ℝ)≤δ)
    (root:((V×V)⊕(V×V))⊕(Bool×V×U)):
    |resourcePatternLoad typedMarkedOccurrenceResources w (fun _ _=>true) root
        (typedMarkedResourceState (ordinaryShiftedPairRims P π d (rawMarkedDeleteRims σ D.edgeFinset)) (rawMarkedPairSpokes π d σ g j))-
      resourcePatternLoad typedMarkedOccurrenceResources w (fun _ _=>true) root
        (typedMarkedResourceState (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j))|≤
      22*((m:ℝ)+1)^4*B*δ/Fintype.card V :=by
  have hh:=ordinary_shifted_marked_load_deletion_stability P π d m hm hn hu w B hB hw σ g j D δ hδ hD root
  rw [typedMarkedPotentialLoad_eq_pattern,typedMarkedPotentialLoad_eq_pattern] at hh
  convert hh using 1 <;> congr! 4
end Oberwolfach
