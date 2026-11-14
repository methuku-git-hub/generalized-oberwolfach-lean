module

public import Oberwolfach.LongEarlyMatchingOnlyWithLists

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem long_ordered_matching_lists_from_uniform_tests
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (r d:ℕ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (ρ αHost ρ₀ lamEarly ζEarly ηListEarly εQ:ℝ)
    (hρ₀:0<ρ₀) (hαHost:0<αHost) (hρlo:ρ₀≤ρ)
    (hlam:0≤lamEarly) (hζ:0≤ζEarly) (hη:0≤ηListEarly)
    (hdegree:∀x,(1/2+αHost)*n≤(P.degree x:ℝ))
    (hNumeric:let βList:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
      βList*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*(1/100:ℝ) ∧
      (lamEarly+2*ζEarly)*n≤βList*n ∧ (n:ℝ)^(3/4:ℝ)≤ηListEarly*n ∧
      ∀(m:ℕ) (ε:ℝ),ε≤βList/32→1/(100*(m:ℝ))≤βList/16→
        βList/2+ε+1/(100*(m:ℝ))+ηListEarly≤lamEarly)
    (hLists:∀(γList pstarList βList lamList ζList:ℝ),
          0≤γList→0≤pstarList→pstarList≤ρ*(1/100)/2→0≤βList→0≤lamList→0≤ζList→
          (∀x,(1/2+γList)*n≤(P.degree x:ℝ))→
          (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstarList^2*n→
          βList*n+(n:ℝ)^(3/4:ℝ)≤γList*pstarList^2*n*(1/100:ℝ)→
          (lamList+2*ζList)*n≤βList*n→
          ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζList*n)→
          ∀(Inner:Finset (Fin n)) (βfinal εInner η:ℝ),0≤βfinal→
          (Inner.card:ℝ)≤εInner*n→(n:ℝ)^(3/4:ℝ)≤η*n→
          βfinal+εInner+1/(100*((r+4:ℕ):ℝ))+η≤lamList→
          let D:=rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e))
          let Dfree:=fun x y=>D x y ∧ ¬Del.Adj x y;
          ∀u,IsExtendingList Dfree (rawReservedSpokeList π d (fun e=>z.1 (Sum.inr e)) u\
            (Inner∪retainedFinalMarkedAt π d (fun e=>z.1 (Sum.inr e))
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) βfinal):
    let βList:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    εQ≤βList/32→1/(100*((r+4:ℕ):ℝ))≤βList/16→
    ∀Inner:Finset (Fin n),(Inner.card:ℝ)≤εQ*n→
    ∀Del:SimpleGraph (Fin n),(∀x,(Del.degree x:ℝ)≤ζEarly*n)→
      LongSampleReservedLists P π d z Del Inner (βList/2) := by
  dsimp only at hNumeric ⊢
  intro hεcap htrim Inner hInner Del hDel
  obtain ⟨herror,hmargin,hbudget,hsub,hnumtrim⟩:=hNumeric
  have hpstar:(ρ₀/200:ℝ)≤ρ*(1/100)/2:=by linarith
  have hβpos:0<(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16:=by positivity
  exact hLists αHost (ρ₀/200) ((min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)
    lamEarly ζEarly hαHost.le (by positivity) hpstar hβpos.le hlam hζ hdegree
    herror hmargin hbudget Del hDel Inner _ εQ ηListEarly (by positivity) hInner hsub (hnumtrim (r+4) εQ hεcap htrim)
end Oberwolfach
