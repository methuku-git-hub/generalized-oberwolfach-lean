module

public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic

@[expose] public section

/-! Exchange each old occurrence with one specified occurrence in its
private copy. All private copies have distinct indices, so the exchanges
form an involution even when the old graph has repeated endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A S W:Type} [DecidableEq W]

def exchangePrivateOccurrence (k:A→W):A⊕((A⊕S)×W)→A⊕((A⊕S)×W)
  | .inl a=>.inr (.inl a,k a)
  | .inr (.inl a,w)=>if w=k a then .inl a else .inr (.inl a,w)
  | .inr (.inr s,w)=>.inr (.inr s,w)

theorem exchangePrivateOccurrence_involutive (k:A→W):Function.Involutive (exchangePrivateOccurrence (S:=S) k):=by
  rintro (a|⟨a|s,w⟩)
  · simp [exchangePrivateOccurrence]
  · by_cases hw:w=k a <;> simp [exchangePrivateOccurrence,hw]
  · rfl

def privateOccurrenceExchange (k:A→W):Equiv.Perm (A⊕((A⊕S)×W)):=
  {toFun:=exchangePrivateOccurrence k, invFun:=exchangePrivateOccurrence k,
   left_inv:=exchangePrivateOccurrence_involutive k, right_inv:=exchangePrivateOccurrence_involutive k}

@[simp] theorem privateOccurrenceExchange_old (k:A→W) (a:A):
    privateOccurrenceExchange (S:=S) k (Sum.inl a)=Sum.inr (Sum.inl a,k a):=rfl

@[simp] theorem privateOccurrenceExchange_private (k:A→W) (a:A) (w:W):
    privateOccurrenceExchange (S:=S) k (Sum.inr (Sum.inl a,w))=
      if w=k a then Sum.inl a else Sum.inr (Sum.inl a,w):=rfl

@[simp] theorem privateOccurrenceExchange_other (k:A→W) (s:S) (w:W):
    privateOccurrenceExchange k (Sum.inr (Sum.inr s,w))=Sum.inr (Sum.inr s,w):=rfl

theorem privateOccurrenceExchange_preserves_type (k:A→W) (j:A⊕((A⊕S)×W)→Bool)
    (hj:∀ a,j (Sum.inl a)=j (Sum.inr (Sum.inl a,k a))):
    ∀ a,j (privateOccurrenceExchange k a)=j a:=by
  rintro (a|⟨a|s,w⟩)
  · exact (hj a).symm
  · by_cases hw:w=k a
    · simp only [privateOccurrenceExchange_private,hw,ite_true];exact hj a
    · simp only [privateOccurrenceExchange_private,if_neg hw]
  · rfl

def spokeOccurrenceReindex: (S⊕((A⊕S)×W))≃(S⊕((S⊕A)×W)):=
  Equiv.sumCongr (Equiv.refl S) (Equiv.prodCongr (Equiv.sumComm A S) (Equiv.refl W))

def privateSpokeExchange (k:S→W):Equiv.Perm (S⊕((A⊕S)×W)):=
  spokeOccurrenceReindex.trans ((privateOccurrenceExchange k).trans spokeOccurrenceReindex.symm)

@[simp] theorem privateSpokeExchange_old (k:S→W) (s:S):
    privateSpokeExchange (A:=A) k (Sum.inl s)=Sum.inr (Sum.inr s,k s):=rfl

@[simp] theorem privateSpokeExchange_private (k:S→W) (s:S) (w:W):
    privateSpokeExchange (A:=A) k (Sum.inr (Sum.inr s,w))=
      if w=k s then Sum.inl s else Sum.inr (Sum.inr s,w):=by
  change spokeOccurrenceReindex.symm (privateOccurrenceExchange k (Sum.inr (Sum.inl s,w))) = _
  rw [privateOccurrenceExchange_private]
  split <;> rfl

@[simp] theorem privateSpokeExchange_other (k:S→W) (a:A) (w:W):
    privateSpokeExchange k (Sum.inr (Sum.inl a,w))=Sum.inr (Sum.inl a,w):=rfl

theorem privateSpokeExchange_preserves_type (k:S→W) (j:S⊕((A⊕S)×W)→Bool)
    (hj:∀ s,j (Sum.inl s)=j (Sum.inr (Sum.inr s,k s))):
    ∀ s,j (privateSpokeExchange k s)=j s:=by
  rintro (s|⟨a|s,w⟩)
  · exact (hj s).symm
  · rfl
  · by_cases hw:w=k s
    · simp only [privateSpokeExchange_private,hw,ite_true];exact hj s
    · simp only [privateSpokeExchange_private,if_neg hw]

end Oberwolfach
