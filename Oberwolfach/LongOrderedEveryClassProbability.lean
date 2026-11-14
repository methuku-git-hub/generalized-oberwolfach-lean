module

public import Oberwolfach.LongOrderedEveryClassSampleTests

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

theorem long_ordered_every_class_probability
    (α ρ₀ δ c:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hCap:LongEveryClassOrientationCap α ρ₀ δ c) :
    ∀d B:ℕ,2≤d→∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (Dnat vsize:ℕ) (β εQ:ℝ) (Q:Vortex U P Dnat β εQ vsize)
    (π:Equiv.Perm (Fin n)) (r K:ℕ) (θ ρ D:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (γLoss σLoss ξClass Δ alpha γ eps:ℝ),
    let βList:ℝ:=(min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16
    0≤εQ→εQ≤((min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/32→
    ρ₀≤ρ→ρ≤1→0<D→0≤θ→θ≤1/100→3≤K→7≤r+4→
    (1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ→(∀u,factorPreparationClass (F u) K=none)→
    ρ*D=2*Fintype.card U→(Dnat:ℝ)=D→P.IsRegularOfDegree Dnat→
    (1/2+α)*(n:ℝ)≤D→0≤ξClass→
    ξClass≤min (min (c/4) (δ/16)) (α*(ρ₀/200)^2/4)→γLoss+ξClass+δ≤Δ→
    ∀(lamEarly ηListEarly:ℝ),0≤lamEarly→0≤Δ→0≤ηListEarly→
    (let βList:ℝ:=(min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤α*(ρ₀/200)^2*n ∧
      βList*n+(n:ℝ)^(3/4:ℝ)≤α*(ρ₀/200)^2*n*(1/100:ℝ) ∧
      (lamEarly+2*Δ)*n≤βList*n ∧ (n:ℝ)^(3/4:ℝ)≤ηListEarly*n ∧
      ∀(m:ℕ) (ε:ℝ),ε≤βList/32→1/(100*(m:ℝ))≤βList/16→
        βList/2+ε+1/(100*(m:ℝ))+ηListEarly≤lamEarly)→
    1/(100*((r+4:ℕ):ℝ))≤βList/16→
    ∀ (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
      (Good:MarkedExpandedActualOutcome (U:=U) π d→Prop) (bound:ℝ),
    (∀z,Good z→LongOrderedEveryClassSampleTests P π r K d θ ρ D F hF z)→
    bound≤μ.probability (fun z=>Good z ∧
      ∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→
        LongEarlyMatchingOnlyForDeletion (r+4) K d θ D alpha γ eps (Δ*n) P π F hF weight w z Del)→
    bound≤μ.probability (fun z=>Good z ∧
      LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξClass z
        (Q.extendedVertices 1) (Q.extendedIndices 1) K B θ D alpha γ eps βList F hF weight w) := by
  intro d B hd
  obtain ⟨N,hN,hOrient⟩:=long_every_class_event_from_ordered_matching_and_tests α ρ₀ δ c hα hρ₀ hCap d B hd
  refine ⟨N,hN,?_⟩
  intro n hn U _ _ _ P Dnat vsize β εQ Q π r K θ ρ D F hF Allowed hAllowed weight w γLoss σLoss ξClass Δ alpha γ eps
  dsimp only
  intro he hecap hrho hrho1 hD hθ hθ1 hK hm hcut hclass hsize hDnat hreg hdeg hξ hξcap hbudget
    lamEarly ηListEarly hlam hΔ hη hNumeric htrim μ Good bound hTests hprob
  apply hprob.trans
  apply finiteLaw_probability_mono_on_support
  intro z hz h
  obtain ⟨hColour,hPath,hLists⟩:=hTests z h.1
  refine ⟨h.1,?_⟩
  exact hOrient n hn P Dnat vsize β εQ Q π r K θ ρ D F hF Allowed hAllowed weight w z γLoss σLoss ξClass Δ alpha γ eps
    he hecap hrho hrho1 hD hθ hθ1 hK hm hcut hclass hsize hDnat hreg hdeg hξ hξcap hbudget hColour hPath
    lamEarly ηListEarly hlam hΔ hη hNumeric htrim hLists h.2
end Oberwolfach
