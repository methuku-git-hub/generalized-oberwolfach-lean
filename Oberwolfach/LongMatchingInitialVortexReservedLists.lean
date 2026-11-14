module

public import Oberwolfach.LongSameSampleMatchingFirstVortexLists
public import Oberwolfach.LongReservedOuterReferenceAlignment
public import Oberwolfach.MarkedExpandedActualSample

@[expose] public section
/-! Instantiate the first-vortex list continuation on the same expanded
sample and deletion as the matching continuation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

def LongSampleReservedLists (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Del:SimpleGraph (Fin n))
    (Inner:Finset (Fin n)) (β:ℝ):Prop :=
  let D:=rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e))
  let Dfree:=fun x y=>D x y ∧ ¬Del.Adj x y
  ∀u,IsExtendingList Dfree (rawReservedSpokeList π d (fun e=>z.1 (Sum.inr e)) u\
    (Inner∪retainedFinalMarkedAt π d (fun e=>z.1 (Sum.inr e))
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) β

theorem long_matching_and_initial_vortex_reserved_lists
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r D m:ℕ) (βQ ε:ℝ)
    (Q:Vortex U P D βQ ε m) (hε:0≤ε)
    (mass:MarkedExpandedActualOutcome (U:=U) π d→ℝ)
    (Good:MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (Match:MarkedExpandedActualOutcome (U:=U) π d→SimpleGraph (Fin n)→ℝ→Prop)
    (Δ ζ αHost αRef ρ₀ βRaw βE:ℝ) (hζΔ:ζ≤Δ)
    (hα:αRef=αHost/2)
    (hβ:βRaw=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)
    (hE:βE=βRaw/2) (hεcap:ε≤βRaw/32)
    (htrim:1/(100*((r+4:ℕ):ℝ))≤βE/8)
    (hSample:∃z,0<mass z ∧ Good z ∧
      (∀(Del:SimpleGraph (Fin n)) (δ:ℝ),(∀x,(Del.degree x:ℝ)≤δ)→δ≤Δ*n→Match z Del δ) ∧
      (let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
       ε≤βList/32→1/(100*((r+4:ℕ):ℝ))≤βList/16→
       ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→
         ∀Inner:Finset (Fin n),(Inner.card:ℝ)≤ε*n→LongSampleReservedLists P π d z Del Inner (βList/2))):
    ∃z,0<mass z ∧ Good z ∧
      ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→
        Match z Del (ζ*n) ∧ LongSampleReservedLists P π d z Del (Q.extendedVertices 1) βE := by
  have ha:=long_reserved_outer_reference_alignment αHost αRef ρ₀ βRaw βE ε (r+4) hα hβ hE hεcap htrim
  obtain ⟨z,hm,hgood,hmatch,hlist⟩:=hSample
  have hlist':∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→
      ∀Inner:Finset (Fin n),(Inner.card:ℝ)≤ε*n→LongSampleReservedLists P π d z Del Inner βE := by
    intro Del hDel Inner hInner
    have hh:=hlist ha.2.1 ha.2.2.1 Del hDel Inner hInner
    simpa only [ha.2.2.2] using hh
  exact long_same_sample_matching_and_first_vortex_lists P D m βQ ε Q hε _ mass Good Match
    (fun z Del Inner=>LongSampleReservedLists P π d z Del Inner βE) Δ ζ hζΔ ⟨z,hm,hgood,hmatch,hlist'⟩
end Oberwolfach
