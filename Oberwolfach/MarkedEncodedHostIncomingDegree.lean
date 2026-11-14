module

public import Oberwolfach.RawMarkedResourceCoordinates
public import Oberwolfach.MarkedSampleOccurrenceMatrix
public import Oberwolfach.MarkedRestrictedDegreeCounts

@[expose] public section
/-! Encoding a simple typed host preserves its total incoming rim degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype E] [Fintype K] [DecidableEq E] [DecidableEq K] [Fintype Γ] [Fintype Color]

theorem marked_encoded_host_incoming_degree
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (τ:RawMarkedOutcome V U Γ Color)
    (tail head:E→V) (ktail khead:K→V)
    (hE:Function.Injective (fun e=>(tail e,head e)))
    (hK:Function.Injective (fun e=>(ktail e,khead e)))
    (hrim:∀mark x y,markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
      if mark then ∃e:K,ktail e=x∧khead e=y else ∃e:E,tail e=x∧head e=y):
    ∀v,((Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v)).card:ℝ)=
      (markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) false true v Finset.univ:ℝ)+
      (markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) true true v Finset.univ:ℝ):=by
  have he:occurrenceMultiplicity tail head=markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) false:=by
    rw [occurrenceMultiplicity_eq_relation tail head hE]
    funext x y
    unfold relationMultiplicity
    have hh:(∃e:E,tail e=x∧head e=y)↔markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) false x y=1:=by
      simpa using (hrim false x y).symm
    simpa only [hh] using markedPhysicalRim_indicator P π (3*d) (fun e=>τ (Sum.inl e)) false x y
  have hk:occurrenceMultiplicity ktail khead=markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) true:=by
    rw [occurrenceMultiplicity_eq_relation ktail khead hK]
    funext x y
    unfold relationMultiplicity
    have hh:(∃e:K,ktail e=x∧khead e=y)↔markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) true x y=1:=by
      simpa using (hrim true x y).symm
    simpa only [hh] using markedPhysicalRim_indicator P π (3*d) (fun e=>τ (Sum.inl e)) true x y
  intro v
  have hc:((Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v)).card:ℝ)=
      occurrenceDegree head v+occurrenceDegree khead v:=by
    rw [←Finset.sum_boole,Fintype.sum_sum_type]
    simp only [Sum.elim_inl,Sum.elim_inr,occurrenceDegree]
  have hedeg:occurrenceDegree head v=(markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) false true v Finset.univ:ℝ):=by
    rw [←occurrenceMultiplicity_col tail head v,he]
    simp only [markedRestrictedDegree,Bool.true_eq,↓reduceIte,Finset.sum_const_zero, Nat.cast_sum]
  have hkdeg:occurrenceDegree khead v=(markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) true true v Finset.univ:ℝ):=by
    rw [←occurrenceMultiplicity_col ktail khead v,hk]
    simp only [markedRestrictedDegree,Bool.true_eq,↓reduceIte,Finset.sum_const_zero, Nat.cast_sum]
  linarith
end Oberwolfach
