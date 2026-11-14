module

public import Oberwolfach.LongSelectedReservedExtendingNoMarkedLoss
public import Oberwolfach.LongEarlyMatchingOnlyWithLists

@[expose] public section
/-! Construct the actual reserved lists on the same sample without the old
inverse-cycle-length requirement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_ordered_matching_lists_no_marked_loss
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)] (hn:2≤n)
    (r K d:ℕ) (hd:0<d) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (ρ αHost ρ₀ lamEarly ζEarly ηListEarly εQ:ℝ)
    (hρ₀:0<ρ₀) (hαHost:0<αHost) (hρlo:ρ₀≤ρ)
    (hlam:0≤lamEarly) (hζ:0≤ζEarly)
    (hdegree:∀x,(1/2+αHost)*n≤(P.degree x:ℝ))
    (hpaths:∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*(ρ*(1/100)/2)^2-
      (n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ))
    (hneighbour:∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) u false
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1/100:ℝ)|<(n:ℝ)^(3/4:ℝ))
    (hNumeric:let βList:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
      βList*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*(1/100:ℝ) ∧
      (lamEarly+2*ζEarly)*n≤βList*n ∧ (n:ℝ)^(3/4:ℝ)≤ηListEarly*n ∧
      ∀ε:ℝ,ε≤βList/32→βList/2+ε≤lamEarly):
    let βList:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    εQ≤βList/32→∀Inner:Finset (Fin n),(Inner.card:ℝ)≤εQ*n→
    ∀Del:SimpleGraph (Fin n),(∀x,(Del.degree x:ℝ)≤ζEarly*n)→
      LongSampleReservedLists P π d z Del Inner (βList/2):=by
  dsimp only at hNumeric ⊢
  intro hεcap Inner hInner Del hDel
  obtain ⟨herror,hmargin,hbudget,hsub,hnumtrim⟩:=hNumeric
  have hpstar:(ρ₀/200:ℝ)≤ρ*(1/100)/2:=by linarith
  have hβpos:0<(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16:=by positivity
  have hdec:referenceWitnessFinDecidable n=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [hdec] at hpaths hneighbour
  letI : DecidableEq (Fin n):=instDecidableEqFin n
  let hJ:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)):=by
    convert z.2 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hresult:=long_selected_reserved_extending_no_marked_loss hn F hF K (r+4) d (by omega) hd θ hθ hθ1 P π z.1
    αHost (ρ₀/200) (ρ*(1/100)/2) ((min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)
    lamEarly ζEarly hαHost.le (by positivity) hpstar hβpos.le hlam hζ hdegree herror hpaths hneighbour
    hmargin hbudget Del hDel _ hJ Inner _ εQ (by positivity) hInner (hnumtrim εQ hεcap)
  dsimp only [LongSampleReservedLists]
  convert hresult using 1 <;> congr! 8
  dsimp [hJ]
  exact (cast_heq _ _).symm
end Oberwolfach
