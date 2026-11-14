module

public import Oberwolfach.LongInnerReserveForbidden
public import Oberwolfach.LongEligibleMarkedIncomingChange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V]
local instance eligibleForbiddenDecEq : DecidableEq V := Classical.decEq V
local instance eligibleForbiddenArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_eligible_forbidden_incoming
    (P:V×V→Prop) (G Bad:SimpleGraph V) (Eligible:V×V→Prop)
    (hhost:∀e,P e→G.Adj e.1 e.2)
    (hbad:∀x y,G.Adj x y→¬Eligible (x,y)→Bad.Adj x y)
    (I:Finset V) (C:Finset (Finset V⊕(V×U))):
    let F:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>
      e.val.1∈I ∨ Sum.inl ({e.val.1,e.val.2}:Finset V)∈C ∨ ¬Eligible e.val)
    (∀e,e.val.1∈I→e∈F) ∧
    (∀e,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→e∈F) ∧
    (∀e,¬Eligible e.val→e∈F) ∧
    (∀v,((F.filter (fun e=>e.val.2=v)).card:ℝ)≤I.card+C.card+Bad.degree v):=by
  intro F
  refine ⟨?_,?_,?_,?_⟩
  · intro e he;simp [F,he]
  · intro e he;simp [F,he]
  · intro e he;simp [F,he]
  · intro v
    let A:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>e.val.2=v ∧ e.val.1∈I)
    let B:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>e.val.2=v ∧ Sum.inl ({e.val.1,e.val.2}:Finset V)∈C)
    let D:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>e.val.2=v ∧ ¬Eligible e.val)
    have hEq:F.filter (fun e=>e.val.2=v)=A∪B∪D:=by
      ext e;simp only [F,A,B,D,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
      tauto
    have hA:A.card≤I.card:=by
      apply incoming_tail_domain_card_le (fun e:{a:V×V // P a}=>e.val.1) (fun e=>e.val.2) I v
      intro a b h;exact Subtype.ext h
    have hB:((B.card:ℕ):ℝ)≤C.card:=marked_reserved_correction_forbidden_bound P C v
    have hD:D.card≤Bad.degree v:=by
      have hs:D.card≤(Bad.neighborFinset v).card:=by
        apply Finset.card_le_card_of_injOn (fun e:{a:V×V // P a}=>e.val.1)
        · intro e he
          have ⟨hv,hel⟩:=(Finset.mem_filter.mp he).2
          apply (Bad.mem_neighborFinset v e.val.1).mpr
          have hh:=hbad e.val.1 e.val.2 (hhost e.val e.property) hel
          simpa only [hv] using hh.symm
        · intro a ha b hb ht
          apply Subtype.ext
          exact Prod.ext ht ((Finset.mem_filter.mp ha).2.1.trans (Finset.mem_filter.mp hb).2.1.symm)
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hs
    have hAB:=Finset.card_union_le A B
    have hABD:=Finset.card_union_le (A∪B) D
    have hU:((A∪B∪D).card:ℝ)≤A.card+B.card+D.card:=by exact_mod_cast (show (A∪B∪D).card≤A.card+B.card+D.card by omega)
    have hAr:(A.card:ℝ)≤I.card:=by exact_mod_cast hA
    have hDr:(D.card:ℝ)≤Bad.degree v:=by exact_mod_cast hD
    rw [hEq]
    linarith only [hU,hAr,hB,hDr]
end Oberwolfach
