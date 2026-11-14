module

public import Oberwolfach.MarkedReservedRimPairCount
public import Oberwolfach.IncomingCandidateLoss

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Nonempty V]
local instance innerReserveVertexDecEq : DecidableEq V := Classical.decEq V

theorem long_inner_reserve_forbidden_incoming
    (P:V×V→Prop) (I:Finset V) (C:Finset (Finset V⊕(V×U))):
    let F:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>e.val.1∈I ∨ Sum.inl ({e.val.1,e.val.2}:Finset V)∈C)
    (∀e,e.val.1∈I→e∈F) ∧
    (∀e,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→e∈F) ∧
    (∀v,((F.filter (fun e=>e.val.2=v)).card:ℝ)≤I.card+C.card):=by
  intro F
  refine ⟨?_,?_,?_⟩
  · intro e he;simp [F,he]
  · intro e he;simp [F,he]
  · intro v
    let A:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>e.val.2=v ∧ e.val.1∈I)
    let B:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>e.val.2=v ∧ Sum.inl ({e.val.1,e.val.2}:Finset V)∈C)
    have hEq:F.filter (fun e=>e.val.2=v)=A∪B:=by
      ext e;simp only [F,A,B,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
      tauto
    have hA:A.card≤I.card:=by
      apply incoming_tail_domain_card_le (fun e:{a:V×V // P a}=>e.val.1) (fun e=>e.val.2) I v
      intro a b h;exact Subtype.ext h
    have hB:((B.card:ℕ):ℝ)≤C.card:=marked_reserved_correction_forbidden_bound P C v
    rw [hEq]
    have hU:=Finset.card_union_le A B
    have hUr:(((A∪B).card:ℕ):ℝ)≤A.card+B.card:=by exact_mod_cast hU
    have hAr:(A.card:ℝ)≤I.card:=by exact_mod_cast hA
    linarith only [hUr,hAr,hB]
end Oberwolfach
