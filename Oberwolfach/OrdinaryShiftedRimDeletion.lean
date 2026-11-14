module

public import Oberwolfach.OrdinaryShiftedMarkedResourceState
public import Oberwolfach.RawMarkedRimDeletion
public import Oberwolfach.PhysicalRimChangeIncidence

@[expose] public section
/-! A later physical-edge deletion removes both ordinary and shifted rim
representations of that edge from the same ordinary sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_delete_rims
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D:Finset (Sym2 V)) (a:(V×V)⊕(V×V)):
    ordinaryShiftedPairRims P π d (rawMarkedDeleteRims σ D) a↔
      ordinaryShiftedPairRims P π d σ a ∧ markedPairPhysical π a∉D :=by
  cases a with
  | inl xy=>
    simp only [ordinaryShiftedPairRims,Sum.elim_inl,markedPairPhysical,rawMarkedDeleteRims]
    split_ifs <;> simp_all
  | inr xy=>
    simp only [ordinaryShiftedPairRims,Sum.elim_inr,markedPairPhysical,rawMarkedDeleteRims]
    split_ifs <;> simp_all

theorem ordinary_shifted_rim_deletion_incidence
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D:SimpleGraph V) (δ:ℝ) (hD:∀x,(D.degree x:ℝ)≤δ):
    let R:=ordinaryShiftedPairRims P π d σ
    let R':=ordinaryShiftedPairRims P π d (rawMarkedDeleteRims σ D.edgeFinset);
    (∀x,(∑e,if ¬(R e↔R' e) ∧ Sum.elim Prod.fst Prod.fst e=x then (1:ℝ) else 0)≤2*δ) ∧
    (∀x,(∑e,if ¬(R e↔R' e) ∧ Sum.elim Prod.snd Prod.snd e=x then (1:ℝ) else 0)≤2*δ) :=by
  intro R R'
  apply physical_rim_change_incidence π D δ hD R R'
  intro e h
  change ¬(ordinaryShiftedPairRims P π d σ e ↔ ordinaryShiftedPairRims P π d (rawMarkedDeleteRims σ D.edgeFinset) e) at h
  rw [ordinary_shifted_delete_rims] at h
  by_contra hn
  exact h (by simp [hn])
end Oberwolfach
