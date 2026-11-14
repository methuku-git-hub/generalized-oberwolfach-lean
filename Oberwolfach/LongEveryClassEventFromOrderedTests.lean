module

public import Oberwolfach.LongEveryClassEventFromOrientationCap
public import Oberwolfach.LongOrderedMatchingListsFromUniformTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_every_class_event_from_ordered_matching_and_tests
    (α ρ₀ δ c:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hCap:LongEveryClassOrientationCap α ρ₀ δ c) :
    ∀d B:ℕ,2≤d→∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (Dnat vsize:ℕ) (β εQ:ℝ) (Q:Vortex U P Dnat β εQ vsize)
    (π:Equiv.Perm (Fin n)) (r K:ℕ) (θ ρ D:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (γLoss σLoss ξClass Δ alpha γ eps:ℝ),
    let βList:ℝ:=(min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16
    let V:=Fin n
    let ω:=z.1
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) z.2 false false
    let T:=Q.extendedVertices 1
    let W:=Q.extendedIndices 1
    let Z:=spanningRestriction (⊤:SimpleGraph V) T
    let p:=ρ*(1/100)/2
    let s:ℝ:=(1/100)/(((r+4):ℕ):ℝ)
    let k:=ρ*s/2
    let a:=longAssignedApproxMarkedWeight F hF K (r+4) θ
    let b:=longAssignedApproxOrdinaryWeight F hF K (r+4) θ
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let u:=2*(∑w,(1-1/100-s-a w-b w))/D
    let Matching:=fun Del:SimpleGraph V=>LongEarlyMatchingListsForDeletion r K d θ D alpha γ eps Δ βList P π F hF weight w z T Del;
    0≤εQ→εQ≤((min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/32→
    ρ₀≤ρ→ρ≤1→0<D→0≤θ→θ≤1/100→3≤K→7≤r+4→
    (1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ→(∀u,factorPreparationClass (F u) K=none)→
    ρ*D=2*Fintype.card U→(Dnat:ℝ)=D→P.IsRegularOfDegree Dnat→
    (1/2+α)*(n:ℝ)≤D→0≤ξClass→
    ξClass≤min (min (c/4) (δ/16)) (α*(ρ₀/200)^2/4)→γLoss+ξClass+δ≤Δ→
    (∀j v,|((∑w,sampledColourOrientation P (fun e=>ω (Sum.inl e)) j v w:ℕ):ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ))→
    (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun w=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false x w ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false w y)).card:ℝ))→
    ∀(lamEarly ηListEarly:ℝ),0≤lamEarly→0≤Δ→0≤ηListEarly→
    (let βList:ℝ:=(min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤α*(ρ₀/200)^2*n ∧
      βList*n+(n:ℝ)^(3/4:ℝ)≤α*(ρ₀/200)^2*n*(1/100:ℝ) ∧
      (lamEarly+2*Δ)*n≤βList*n ∧ (n:ℝ)^(3/4:ℝ)≤ηListEarly*n ∧
      ∀(m:ℕ) (ε:ℝ),ε≤βList/32→1/(100*(m:ℝ))≤βList/16→
        βList/2+ε+1/(100*(m:ℝ))+ηListEarly≤lamEarly)→
    1/(100*((r+4:ℕ):ℝ))≤βList/16→
    (∀(γList pstarList βList lamList ζList:ℝ),
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
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) βfinal)→
    (∀Del:SimpleGraph V,(∀v,(Del.degree v:ℝ)≤Δ*n)→
      LongEarlyMatchingOnlyForDeletion (r+4) K d θ D alpha γ eps (Δ*n) P π F hF weight w z Del)→
    LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξClass z T W K B θ D alpha γ eps βList F hF weight w := by
  intro d B hd
  obtain ⟨N,hN,hOrient⟩:=hCap d B hd
  refine ⟨N,hN,?_⟩
  intro n hn U _ _ _ P Dnat vsize β εQ Q π r K θ ρ D F hF Allowed hAllowed weight w z γLoss σLoss ξClass Δ alpha γ eps
  dsimp only
  intro he hecap hrho hrho1 hD hθ hθ1 hK hm hcut hclass hsize hDnat hreg hdeg hξ hξcap hbudget hColour hPath
    lamEarly ηListEarly hlam hΔ hη hNumeric htrim hLists hOnly
  have hPList:∀x,(1/2+α)*n≤(P.degree x:ℝ):=by
    intro x
    rw [hreg x]
    simpa only [hDnat] using hdeg
  have hInner:((Q.extendedVertices 1).card:ℝ)≤εQ*n:=by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_upper he
  have hList:=long_ordered_matching_lists_from_uniform_tests r d P π z ρ α ρ₀ lamEarly Δ ηListEarly εQ
    hρ₀ hα hrho hlam hΔ hη hPList hNumeric hLists hecap htrim (Q.extendedVertices 1) hInner
  have hMatching:=long_early_matching_only_with_lists r K d θ D alpha γ eps Δ
    ((min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) P π F hF weight w z (Q.extendedVertices 1) hOnly hList
  have hh:=hOrient n hn P Dnat vsize β εQ Q π r K θ ρ D F hF Allowed hAllowed weight w z γLoss σLoss ξClass Δ alpha γ eps
    ((min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)
    he hecap hrho hrho1 hD hθ hθ1 hK hm hcut hclass hsize hDnat hreg hdeg hξ hξcap hbudget hColour hPath hMatching
  exact hh
end Oberwolfach
