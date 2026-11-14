module

public import Oberwolfach.MarkedPhysicalDeletionExtensions

@[expose] public section

/-! Host intersection counts after deleting a specified spoke relation.
Losses are the realized row and column degrees of that relation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem finite_predicate_delete_relation {A B:Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (P:A→Prop) (S:Finset B) (F:A→B→Prop) (d:ℕ)
    (hF:∀ b∈S,(Finset.univ.filter (fun a=>F a b)).card≤d):
    ((Finset.univ.filter P).card:ℝ)-S.card*d≤
      (Finset.univ.filter (fun a=>P a∧∀ b∈S,¬F a b)).card:=by
  let T:=S.biUnion (fun b=>Finset.univ.filter (fun a=>F a b))
  have hT:T.card≤S.card*d:=Finset.card_biUnion_le.trans
    ((Finset.sum_le_sum (fun b hb=>hF b hb)).trans_eq (by simp [Nat.mul_comm]))
  have hc:Finset.univ.filter P⊆Finset.univ.filter (fun a=>P a∧∀ b∈S,¬F a b)∪T:=by
    intro a ha
    by_cases hb:∃ b∈S,F a b
    · obtain ⟨b,hb,hF⟩:=hb
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hF⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2,
        fun b hbS hf=>hb ⟨b,hbS,hf⟩⟩)
  have hh:(Finset.univ.filter P).card≤
      (Finset.univ.filter (fun a=>P a∧∀ b∈S,¬F a b)).card+S.card*d:=
    (Finset.card_le_card hc).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hT _))
  have hh':((Finset.univ.filter P).card:ℝ)≤
      (Finset.univ.filter (fun a=>P a∧∀ b∈S,¬F a b)).card+(S.card:ℝ)*d:=by exact_mod_cast hh
  linarith only [hh']

theorem markedSpokesTo_delete (F:V→U→Prop) (j:Bool) (P:Finset U) (x:V):
    markedSpokesTo (fun x u=>H₀ x u∧¬F x u) (fun x u=>HK x u∧¬F x u) j P x↔
      markedSpokesTo H₀ HK j P x∧∀ u∈P,¬F x u:=by
  cases j <;> simp only [markedSpokesTo,Bool.false_eq_true,ite_false,ite_true] <;> aesop

theorem marked_host_extensions_after_spoke_deletion
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (F:V→U→Prop) (drow dcol:ℕ)
    (hr:∀ v,(Finset.univ.filter (F v)).card≤drow)
    (hc:∀ u,(Finset.univ.filter (fun v=>F v u)).card≤dcol):
    MarkedHostExtensionCounts tail head ktail khead
      (fun x u=>H₀ x u∧¬F x u) (fun x u=>HK x u∧¬F x u) π b l
      (c-2*dcol) (ch-(l+11)*drow):=by
  have hrow (A:V→Prop) (k:Bool) (P:Finset U) (hP:P.card≤2)
      (hcount:c≤((Finset.univ.filter (fun v=>A v∧markedSpokesTo H₀ HK k P v)).card:ℝ)):
      c-2*dcol≤((Finset.univ.filter (fun v=>A v∧
        markedSpokesTo (fun x u=>H₀ x u∧¬F x u) (fun x u=>HK x u∧¬F x u) k P v)).card:ℝ):=by
    have hh:=finite_predicate_delete_relation (fun v=>A v∧markedSpokesTo H₀ HK k P v) P F dcol (fun u _=>hc u)
    have hp:(P.card:ℝ)*dcol≤2*dcol:=mul_le_mul_of_nonneg_right (by exact_mod_cast hP) (by positivity)
    have he:Finset.univ.filter (fun v=>A v∧markedSpokesTo (fun x u=>H₀ x u∧¬F x u) (fun x u=>HK x u∧¬F x u) k P v)=
        Finset.univ.filter (fun v=>(A v∧markedSpokesTo H₀ HK k P v)∧∀ u∈P,¬F v u):=by
      ext v;simp only [Finset.mem_filter,markedSpokesTo_delete];tauto
    rw [he]
    calc
      c-2*dcol≤((Finset.univ.filter (fun v=>A v∧markedSpokesTo H₀ HK k P v)).card:ℝ)-P.card*dcol:=by
        linarith only [hcount,hp]
      _≤_:=by convert hh using 1 <;> congr!
  constructor
  · intro j k x P hP
    exact hrow (fun v=>markedArcPresent tail head ktail khead j x v) k P hP (Q.outgoing j k x P hP)
  · intro j k x P hP
    exact hrow (fun v=>markedArcPresent tail head ktail khead j v x) k P hP (Q.incoming j k x P hP)
  · intro k x y P hxy hP
    have hh:=hrow (fun v=>markedArcPresent tail head ktail khead false x v∧markedArcPresent tail head ktail khead false y v)
      k P hP (by simpa only [and_assoc] using Q.twoOutgoing k x y P hxy hP)
    simpa only [and_assoc] using hh
  · intro j k x y P hxy hP
    have hh:=hrow (fun v=>markedArcPresent tail head ktail khead j v x∧markedArcPresent tail head ktail khead j v y)
      k P hP (by simpa only [and_assoc] using Q.twoIncoming j k x y P hxy hP)
    simpa only [and_assoc] using hh
  · intro k x y P hxy hP
    have hh:=hrow (fun v=>markedArcPresent tail head ktail khead false x v∧markedArcPresent tail head ktail khead false v y)
      k P hP (by simpa only [and_assoc] using Q.twoStep k x y P hxy hP)
    simpa only [and_assoc] using hh
  · intro A B hd hab hsep
    have hh:=finite_predicate_delete_relation (fun u=>(∀ v∈A,H₀ v u)∧∀ v∈B,HK v u)
      (A∪B) (fun u v=>F v u) drow (fun v _=>hr v)
    have he:Finset.univ.filter (fun u=>(∀ v∈A,H₀ v u∧¬F v u)∧∀ v∈B,HK v u∧¬F v u)=
        Finset.univ.filter (fun u=>((∀ v∈A,H₀ v u)∧∀ v∈B,HK v u)∧∀ v∈A∪B,¬F v u):=by
      ext u;simp only [Finset.mem_filter,Finset.mem_union];aesop
    have hp:((A∪B).card:ℝ)*drow≤(l+11)*drow:=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.card_union_le A B).trans hab) (by positivity)
    have hq:ch≤((Finset.univ.filter (fun u=>(∀ v∈A,H₀ v u)∧∀ v∈B,HK v u)).card:ℝ):=by
      convert Q.hubs A B hd hab hsep using 1 <;> congr!
    have hg:ch-(l+11)*drow≤((Finset.univ.filter (fun u=>(∀ v∈A,H₀ v u∧¬F v u)∧∀ v∈B,HK v u∧¬F v u)).card:ℝ):=by
      rw [he]
      calc
        ch-(l+11)*drow≤((Finset.univ.filter (fun u=>(∀ v∈A,H₀ v u)∧∀ v∈B,HK v u)).card:ℝ)-(A∪B).card*drow:=by
          linarith only [hq,hp]
        _≤_:=by convert hh using 1 <;> congr!
    convert hg using 1 <;> congr!

end Oberwolfach
