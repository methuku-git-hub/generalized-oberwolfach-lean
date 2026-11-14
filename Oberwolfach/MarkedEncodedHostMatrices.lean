module

public import Oberwolfach.MarkedRawHostArcEquivalences
public import Oberwolfach.MarkedSampleOccurrenceMatrix

@[expose] public section

/-! The rim matrices of the encoded outcome are exactly the original
ordinary and marked occurrence matrices, with directions unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]

theorem marked_encoded_host_matrices
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e)))
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (hI:∀ v,π v∈I↔v∈I)
    (hAgree:∀ mark x y,x∈I → y∈I →
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y))) :
    let τ:=rawMarkedEncodeHost tail head ktail khead π σ I;
    markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) false=occurrenceMultiplicity tail head ∧
    markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) true=occurrenceMultiplicity ktail khead := by
  intro τ
  have heinj:Function.Injective (fun e:E=>(tail e,head e)):=by
    intro a b hab
    have hh:(Sum.inl a:E⊕K)=Sum.inl b:=hp (by
      have ht:tail a=tail b:=congrArg Prod.fst hab
      have hh:head a=head b:=congrArg Prod.snd hab
      simpa only [markedPhysicalEdge,Sum.elim_inl,ht,hh])
    exact Sum.inl.inj hh
  have hkinj:Function.Injective (fun e:K=>(ktail e,khead e)):=by
    intro a b hab
    have hh:(Sum.inr a:E⊕K)=Sum.inr b:=hp (by
      have ht:ktail a=ktail b:=congrArg Prod.fst hab
      have hh:khead a=khead b:=congrArg Prod.snd hab
      simpa only [markedPhysicalEdge,Sum.elim_inr,ht,hh])
    exact Sum.inr.inj hh
  rw [occurrenceMultiplicity_eq_relation tail head heinj,
    occurrenceMultiplicity_eq_relation ktail khead hkinj]
  constructor
  · funext x y
    rw [←markedPhysicalRim_indicator]
    unfold relationMultiplicity
    dsimp only [τ]
    simp only [rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree false x y,Bool.false_eq_true,ite_false] <;> split_ifs <;> rfl
  · funext x y
    rw [←markedPhysicalRim_indicator]
    unfold relationMultiplicity
    dsimp only [τ]
    simp only [rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree true x y,ite_true] <;> split_ifs <;> rfl

end Oberwolfach
