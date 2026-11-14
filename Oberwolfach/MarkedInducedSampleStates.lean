module

public import Oberwolfach.RawMarkedResourceCoordinates
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Inducing on a permutation-invariant row set restricts both auxiliary
endpoints, including the marked closing arc's shifted physical endpoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem markedPhysicalRim_spanningRestriction_iff
    (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ) (X:Finset V)
    (hX:∀ x,π x∈X↔x∈X) (σ:Sym2 V→Option (Bool×Bool)) (j:Bool) (x y:V):
    markedPhysicalRim (spanningRestriction P X) π b σ j x y=1↔
      markedPhysicalRim P π b σ j x y=1∧x∈X∧y∈X:=by
  rw [markedPhysicalRim_eq_one_iff,markedPhysicalRim_eq_one_iff,spanningRestriction_adj]
  cases j <;> simp only [Bool.false_eq_true,ite_false,ite_true,hX] <;> tauto

theorem rawMarkedPairRims_spanningRestriction
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (X:Finset V)
    (hX:∀ x,π x∈X↔x∈X) (σ:RawMarkedOutcome V U Γ Color):
    rawMarkedPairRims (spanningRestriction P X) π d σ=
      (fun a=>rawMarkedPairRims P π d σ a∧Sum.elim Prod.fst Prod.fst a∈X∧Sum.elim Prod.snd Prod.snd a∈X):=by
  funext a
  apply propext
  cases a <;> exact markedPhysicalRim_spanningRestriction_iff P π (3*d) X hX _ _ _ _

theorem markedSampleArc_spanningRestriction_support
    (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ) (X:Finset V)
    (hX:∀ x,π x∈X↔x∈X) (σ:Sym2 V→Option (Bool×Bool)) (j:Bool)
    (e:MarkedSampleArc (spanningRestriction P X) π b σ j):
    e.val.1∈X∧e.val.2∈X:=
  ((markedPhysicalRim_spanningRestriction_iff P π b X hX σ j _ _).mp e.property).2

end Oberwolfach
