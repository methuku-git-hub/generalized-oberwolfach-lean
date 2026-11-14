module

public import Oberwolfach.MarkedBalanceReservationEvent
public import Oberwolfach.IncidentOppositeEndpointBound
public import Oberwolfach.MarkedBalanceTermRestriction
public import Oberwolfach.MarkedBalanceTermDegrees
public import Oberwolfach.OccurrenceDegreeDeletion

@[expose] public section

/-! The actual degree lost by deleting the inner pair and sampled boundary.
One event controls all six incidence terms and all ambient roots. Its error
is additive and is not multiplied by the sampling probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reservation_count_loss_upper (a i d p ε A I:ℝ) (hp:0 ≤ p) (hp1:p ≤ 1)
    (hi:0 ≤ i) (hA:0 ≤ A) (ha:a ≤ A) (hI:i ≤ I) (inside:Bool)
    (herr:|d-(if inside then (1-p)*(a-i) else a-p*i)| ≤ ε):
    a-d ≤ ε+p*A+I:=by
  have hb:=mul_le_mul_of_nonneg_left ha hp
  have hpi:=mul_le_mul_of_nonneg_right hp hi
  have hpi1:=mul_le_mul_of_nonneg_right hp1 hi
  cases inside <;> simp only [Bool.false_eq_true,ite_false,ite_true] at herr
  · have he:=(abs_le.mp herr).1
    nlinarith only [he,hI,hpi1,mul_nonneg hp hA]
  · have he:=(abs_le.mp herr).1
    nlinarith only [he,hb,hI,hpi]

theorem marked_reservation_deleted_count_event (ε:ℝ) (hε:0<ε) (q:ℕ):
    ∃ N:ℕ,∀ (V U E K:Type) [Fintype V] [Fintype U] [Fintype E] [Fintype K]
      [DecidableEq V] [DecidableEq U],N ≤ Fintype.card (V⊕U)→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    ∀ (X:Finset V) (Z:Finset U) (p:ℝ) (hp:0 ≤ p) (hp1:p ≤ 1),
    1-1/(Fintype.card (V⊕U):ℝ)^q ≤ 
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>∀ (r:V⊕U) (j:Fin 6),
        let keep:=markedActiveRetained
          (fun e=>¬markedBoundaryRimAllowed π X σ false (tail e) (head e))
          (fun e=>¬markedBoundaryRimAllowed π X σ true (ktail e) (khead e))
          (fun x u=>H₀ x u∧¬markedBoundarySpokeAllowed X Z σ x u)
          (fun x u=>HK x u∧¬markedBoundarySpokeAllowed X Z σ x u);
        (((markedBalanceTermSet tail head ktail khead H₀ HK r j).filter (fun a=>¬keep a)).card:ℝ) ≤ 
          (ε+4*p)*Fintype.card (V⊕U)+6*(ordinaryInnerVertices X Z).card):=by
  obtain ⟨N,hN⟩:=marked_balance_reservation_common_event ε hε q
  refine ⟨N,?_⟩
  intro V U E K _ _ _ _ _ _ hn tail head ktail khead H₀ HK π hphys X Z p hp hp1
  apply (hN V U E K hn tail head ktail khead H₀ HK π hphys X Z p hp hp1).trans
  apply finiteLaw_probability_mono
  intro σ hσ r j keep
  let A:=markedBalanceTermSet tail head ktail khead H₀ HK r j
  let I:=A.filter (fun a=>(if markedActiveAuxTail tail ktail H₀ HK a=r
    then markedActiveAuxHead head khead H₀ HK a else markedActiveAuxTail tail ktail H₀ HK a)∈ordinaryInnerVertices X Z)
  have hAc:(A.card:ℝ) ≤ 4*Fintype.card (V⊕U):=by
    exact_mod_cast markedBalanceTermSet_card tail head ktail khead H₀ HK π hphys r j
  have hIc:(I.card:ℝ) ≤ 6*(ordinaryInnerVertices X Z).card:=by
    exact_mod_cast marked_balance_inner_term_card tail head ktail khead H₀ HK π hphys X Z r j
  have hc:=Finset.card_filter_add_card_filter_not (s:=A) keep
  have hcR:((A.filter keep).card:ℝ)+(A.filter (fun a=>¬keep a)).card=A.card:=by exact_mod_cast hc
  have he:=reservation_count_loss_upper A.card I.card (A.filter keep).card p
    (ε*Fintype.card (V⊕U)) (4*Fintype.card (V⊕U)) (6*(ordinaryInnerVertices X Z).card)
    hp hp1 (by positivity) (by positivity) hAc hIc (decide (r∈ordinaryInnerVertices X Z)) (by
      simpa only [decide_eq_true_eq] using hσ r j)
  change ((A.filter (fun a=>¬keep a)).card:ℝ) ≤ _
  nlinarith only [he,hcR]
end Oberwolfach
