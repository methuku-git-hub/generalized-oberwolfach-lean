module

public import Oberwolfach.MarkedPackingFiniteBalance

@[expose] public section

/-! Exact balances only at vertices outside an inner pair. A reserved
inner star need not be divisible, so its removal does not justify global
divisibility of the active host. These are precisely the local identities
needed to complete its boundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

structure MarkedOutsideBalance (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (X:Finset V) (Z:Finset U):Prop where
  directed:∀ v,v∉X→(A.filter (fun a=>Sum.elim head khead a=v)).card=
    (A.filter (fun a=>Sum.elim tail ktail a=v)).card
  row:∀ v,v∉X→(A.filter (fun a=>Sum.elim head khead a=v)).card=(S.filter (fun s=>s.1=v)).card
  marked:∀ v,v∉X→(A.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card=
    (S.filter (fun s=>s.1=v∧HK s.1 s.2)).card
  hub:∀ u,u∉Z→(S.filter (fun s=>s.2=u∧¬HK s.1 s.2)).card=
    m*(S.filter (fun s=>s.2=u∧HK s.1 s.2)).card

variable {tail head:E→V} {ktail khead:K→V} {HK:V→U→Prop} {m:ℕ}

theorem MarkedRemainderDivisible.outside (A:Finset (E⊕K)) (S:Finset (V×U))
    (h:MarkedRemainderDivisible tail head ktail khead HK A S m) (X:Finset V) (Z:Finset U):
    MarkedOutsideBalance tail head ktail khead HK A S m X Z:=
  ⟨fun v _=>h.directed v,fun v _=>h.row v,fun v _=>h.marked v,fun u _=>h.hub u⟩

theorem MarkedOutsideBalance.sdiff
    (A B:Finset (E⊕K)) (S R:Finset (V×U)) (X:Finset V) (Z:Finset U)
    (hA:B⊆A) (hS:R⊆S)
    (h:MarkedOutsideBalance tail head ktail khead HK A S m X Z)
    (h':MarkedRemainderDivisible tail head ktail khead HK B R m):
    MarkedOutsideBalance tail head ktail khead HK (A\B) (S\R) m X Z:=by
  constructor
  · intro v hv
    rw [finite_filter_sdiff_card A B hA,finite_filter_sdiff_card A B hA,h.directed v hv,h'.directed v]
  · intro v hv
    rw [finite_filter_sdiff_card A B hA,finite_filter_sdiff_card S R hS,h.row v hv,h'.row v]
  · intro v hv
    rw [finite_filter_sdiff_card A B hA,finite_filter_sdiff_card S R hS,h.marked v hv,h'.marked v]
  · intro u hu
    rw [finite_filter_sdiff_card S R hS,finite_filter_sdiff_card S R hS,h.hub u hu,h'.hub u,Nat.mul_sub_left_distrib]

theorem MarkedOutsideBalance.remove_inner
    (A B:Finset (E⊕K)) (S R:Finset (V×U)) (X:Finset V) (Z:Finset U)
    (hB:∀ a∈B,Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)
    (hR:∀ s∈R,s.1∈X∧s.2∈Z)
    (h:MarkedOutsideBalance tail head ktail khead HK A S m X Z):
    MarkedOutsideBalance tail head ktail khead HK (A\B) (S\R) m X Z:=by
  have hE (v:V) (hv:v∉X) (p:E⊕K→Prop) (hp:∀ a,p a→Sum.elim tail ktail a=v∨Sum.elim head khead a=v):
      (A\B).filter p=A.filter p:=by
    ext a
    simp only [Finset.mem_filter,Finset.mem_sdiff]
    constructor
    · tauto
    · rintro ⟨ha,hp'⟩
      refine ⟨⟨ha,?_⟩,hp'⟩
      intro hb
      rcases hp a hp' with ht|hh
      · exact hv (ht ▸ (hB a hb).1)
      · exact hv (hh ▸ (hB a hb).2)
  have hV (v:V) (hv:v∉X) (p:V×U→Prop) (hp:∀ s,p s→s.1=v):
      (S\R).filter p=S.filter p:=by
    ext s
    simp only [Finset.mem_filter,Finset.mem_sdiff]
    constructor
    · tauto
    · rintro ⟨hs,hp'⟩
      exact ⟨⟨hs,fun hr=>hv (hp s hp' ▸ (hR s hr).1)⟩,hp'⟩
  have hU (u:U) (hu:u∉Z) (p:V×U→Prop) (hp:∀ s,p s→s.2=u):
      (S\R).filter p=S.filter p:=by
    ext s
    simp only [Finset.mem_filter,Finset.mem_sdiff]
    constructor
    · tauto
    · rintro ⟨hs,hp'⟩
      exact ⟨⟨hs,fun hr=>hu (hp s hp' ▸ (hR s hr).2)⟩,hp'⟩
  constructor
  · intro v hv
    have h1:=congrArg Finset.card (hE v hv (fun a=>Sum.elim head khead a=v) (fun a ha=>Or.inr ha))
    have h2:=congrArg Finset.card (hE v hv (fun a=>Sum.elim tail ktail a=v) (fun a ha=>Or.inl ha))
    have h3:=h.directed v hv
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_sdiff] at h1 h2 h3 ⊢
    exact h1.trans (h3.trans h2.symm)
  · intro v hv
    have h1:=congrArg Finset.card (hE v hv (fun a=>Sum.elim head khead a=v) (fun a ha=>Or.inr ha))
    have h2:=congrArg Finset.card (hV v hv (fun s=>s.1=v) (fun s hs=>hs))
    have h3:=h.row v hv
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_sdiff] at h1 h2 h3 ⊢
    exact h1.trans (h3.trans h2.symm)
  · intro v hv
    have h1:=congrArg Finset.card (hE v hv (fun a=>Sum.elim head khead a=v∧markedArcType a=true) (fun a ha=>Or.inr ha.1))
    have h2:=congrArg Finset.card (hV v hv (fun s=>s.1=v∧HK s.1 s.2) (fun s hs=>hs.1))
    have h3:=h.marked v hv
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_sdiff] at h1 h2 h3 ⊢
    exact h1.trans (h3.trans h2.symm)
  · intro u hu
    have h1:=congrArg Finset.card (hU u hu (fun s=>s.2=u∧¬HK s.1 s.2) (fun s hs=>hs.1))
    have h2:=congrArg (fun F:Finset (V×U)=>m*F.card) (hU u hu (fun s=>s.2=u∧HK s.1 s.2) (fun s hs=>hs.1))
    have h3:=h.hub u hu
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_sdiff] at h1 h2 h3 ⊢
    exact h1.trans (h3.trans h2.symm)

end Oberwolfach
