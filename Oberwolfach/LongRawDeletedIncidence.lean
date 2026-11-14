module

public import Oberwolfach.LongRawSurvivingStateIdentity
public import Oberwolfach.MarkedPotentialPhysicalDeletion

@[expose] public section
/-! The actual deleted typed resources have controlled auxiliary tail and
head incidence, by the physical deletion graph's degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def longRawResourceTail (z:LongRawHubResource n U):Fin n:=
  match z with
  | Sum.inl e => Sum.elim Prod.fst Prod.fst e
  | Sum.inr (_,v,_) => v

def longRawResourceHead (z:LongRawHubResource n U):Fin n:=
  match z with
  | Sum.inl e => Sum.elim Prod.snd Prod.snd e
  | Sum.inr (_,v,_) => v

theorem long_raw_deleted_resource_iff_rim_changed
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (z:LongRawHubResource n U):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let Deleted:=T.filter (fun z=>∃edge,typedResourcePhysical π
      ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge ∧ edge∈D.edgeFinset)
    z∈Deleted ↔ ∃e,z=Sum.inl e ∧
      ¬(rawMarkedPairRims P π d raw e↔rawMarkedPairRims P π d (rawMarkedDeleteRims raw D.edgeFinset) e) :=by
  intro T Deleted
  cases z with
  | inl e =>
    cases e with
    | inl e =>
      simp [Deleted,T,mem_bernoulliVertexSet,longRawHubState,typedMarkedResourceState,
        rawMarkedDeleteRims_rims,typedResourcePhysical,markedResourceTypeEquiv,markedPairPhysical]
    | inr e =>
      simp [Deleted,T,mem_bernoulliVertexSet,longRawHubState,typedMarkedResourceState,
        rawMarkedDeleteRims_rims,typedResourcePhysical,markedResourceTypeEquiv,markedPairPhysical]
  | inr z =>
    rcases z with ⟨b,v,u⟩
    simp [Deleted,T,typedResourcePhysical,markedResourceTypeEquiv]
theorem long_raw_deleted_resource_incidence_bound
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (δ:ℝ)
    (hD:∀x,(D.degree x:ℝ)≤δ):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let Deleted:=T.filter (fun z=>∃edge,typedResourcePhysical π
      ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge ∧ edge∈D.edgeFinset)
    (∀x,(∑a,if a∈Deleted ∧ longRawResourceTail a=x then (1:ℝ) else 0)≤2*δ) ∧
    (∀x,(∑a,if a∈Deleted ∧ longRawResourceHead a=x then (1:ℝ) else 0)≤2*δ) :=by
  intro T Deleted
  have hi:=marked_rim_physical_deletion_incidence P π d raw D δ hD
  have hz (z:LongRawHubResource n U):z∈Deleted ↔ ∃e,z=Sum.inl e ∧
      ¬(rawMarkedPairRims P π d raw e↔rawMarkedPairRims P π d (rawMarkedDeleteRims raw D.edgeFinset) e):=
    long_raw_deleted_resource_iff_rim_changed P D π d raw g j z
  constructor
  · intro x
    have he:(∑a,if a∈Deleted ∧ longRawResourceTail a=x then (1:ℝ) else 0)=
        ∑e:((Fin n×Fin n)⊕(Fin n×Fin n)),
          if ¬(rawMarkedPairRims P π d raw e↔rawMarkedPairRims P π d (rawMarkedDeleteRims raw D.edgeFinset) e) ∧
            Sum.elim Prod.fst Prod.fst e=x then (1:ℝ) else 0 :=by
      rw [Fintype.sum_sum_type]
      simp [hz,longRawResourceTail]
    rw [he]
    convert hi.1 x using 1
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> rfl
  · intro x
    have he:(∑a,if a∈Deleted ∧ longRawResourceHead a=x then (1:ℝ) else 0)=
        ∑e:((Fin n×Fin n)⊕(Fin n×Fin n)),
          if ¬(rawMarkedPairRims P π d raw e↔rawMarkedPairRims P π d (rawMarkedDeleteRims raw D.edgeFinset) e) ∧
            Sum.elim Prod.snd Prod.snd e=x then (1:ℝ) else 0 :=by
      rw [Fintype.sum_sum_type]
      simp [hz,longRawResourceHead]
    rw [he]
    convert hi.2 x using 1
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> rfl
end Oberwolfach
