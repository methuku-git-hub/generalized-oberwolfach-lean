module

public import Oberwolfach.MarkedFiniteDomainBalance

@[expose] public section

/-! A graph supported on the inner pair has zero incidence, hence zero
full or opposite-endpoint balance, at every root outside that pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteBalance_zero_of_support
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (I:Finset V) (J:Finset U)
    (hA:∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)
    (hS:∀ s∈S,s.1∈I∧s.2∈J)
    (z:V⊕U) (hz:Sum.elim (fun v=>v∉I) (fun u=>u∉J) z) (i:Fin 4):
    markedFiniteBalance tail head ktail khead HK A S m z i=0:=by
  cases z with
  | inl v=>
    change v∉I at hz
    have ha (p:(E⊕K)→Prop) [DecidablePred p]
        (hp:∀ a,p a→Sum.elim tail ktail a=v∨Sum.elim head khead a=v):A.filter p=∅:=by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha hh
      rcases hp a hh with hh|hh
      · exact hz (hh ▸ (hA a ha).1)
      · exact hz (hh ▸ (hA a ha).2)
    have hs (p:(V×U)→Prop) [DecidablePred p] (hp:∀ s,p s→s.1=v):S.filter p=∅:=by
      apply Finset.filter_eq_empty_iff.mpr
      intro s hs hh
      exact hz (hp s hh ▸ (hS s hs).1)
    have h0:=ha (fun a=>Sum.elim tail ktail a=v) (fun _ h=>Or.inl h)
    have h1:=ha (fun a=>Sum.elim head khead a=v) (fun _ h=>Or.inr h)
    have h2:=ha (fun a=>Sum.elim head khead a=v∧markedArcType a=true) (fun _ h=>Or.inr h.1)
    have h3:=hs (fun s=>s.1=v) (fun _ h=>h)
    have h4:=hs (fun s=>s.1=v∧HK s.1 s.2) (fun _ h=>h.1)
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ',
      h0,h1,h2,h3,h4,Finset.card_empty,Nat.cast_zero,sub_zero]
  | inr u=>
    change u∉J at hz
    have hs (p:(V×U)→Prop) [DecidablePred p] (hp:∀ s,p s→s.2=u):S.filter p=∅:=by
      apply Finset.filter_eq_empty_iff.mpr
      intro s hs hh
      exact hz (hp s hh ▸ (hS s hs).2)
    have h0:=hs (fun s=>s.2=u∧¬HK s.1 s.2) (fun _ h=>h.1)
    have h1:=hs (fun s=>s.2=u∧HK s.1 s.2) (fun _ h=>h.1)
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ',
      h0,h1,Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero]

theorem markedFiniteDomainBalance_zero_of_support
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (I:Finset V) (J:Finset U)
    (hA:∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)
    (hS:∀ s∈S,s.1∈I∧s.2∈J) (X:Finset V) (Z:Finset U)
    (z:V⊕U) (hz:Sum.elim (fun v=>v∉I) (fun u=>u∉J) z) (i:Fin 4):
    markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i=0:=by
  cases z with
  | inl v=>
    dsimp only [markedFiniteDomainBalance]
    exact markedFiniteBalance_zero_of_support tail head ktail khead HK _ _ m I J
      (fun a ha=>hA a (Finset.mem_filter.mp ha).1) (fun s hs=>hS s (Finset.mem_filter.mp hs).1)
      (Sum.inl v) hz i
  | inr u=>
    dsimp only [markedFiniteDomainBalance]
    exact markedFiniteBalance_zero_of_support tail head ktail khead HK _ _ m I J
      (by intro a ha;exact (Finset.notMem_empty _ ha).elim)
      (fun s hs=>hS s (Finset.mem_filter.mp hs).1) (Sum.inr u) hz i

end Oberwolfach
