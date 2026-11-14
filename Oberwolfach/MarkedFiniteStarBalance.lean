module

public import Oberwolfach.MarkedFiniteDomainBalance
public import Oberwolfach.MarkedStarRestrictionBalances

@[expose] public section

/-! The balance of a reserved star at a row or hub outside that star is
exactly the balance restricted at the opposite endpoint. At a row or hub
of the star it is the full balance of the graph from which the star was
reserved. These are identities, without a divisibility assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem finite_filter_agree_on {A:Type} (F:Finset A) (p q r:A→Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (h:∀ a∈F,r a→(p a↔q a)):
    (F.filter p).filter r=(F.filter q).filter r:=by
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨ha,hp⟩,hr⟩;exact ⟨⟨ha,(h a ha hr).mp hp⟩,hr⟩
  · rintro ⟨⟨ha,hq⟩,hr⟩;exact ⟨⟨ha,(h a ha hr).mpr hq⟩,hr⟩

theorem markedFiniteBalance_star_outside
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (T:Finset V) (W:Finset U)
    (z:V⊕U) (hz:Sum.elim (fun v=>v∉T) (fun u=>u∉W) z) (i:Fin 4):
    markedFiniteBalance tail head ktail khead HK
      (A.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T))
      (S.filter (fun s=>s.1∈T∨s.2∈W)) m z i=
      markedFiniteDomainBalance tail head ktail khead HK A S m T W z i:=by
  cases z with
  | inl v=>
    change v∉T at hz
    have ha (r:(E⊕K)→Prop) [DecidablePred r]
        (hr:∀ a,r a→Sum.elim tail ktail a=v∨Sum.elim head khead a=v):
        (A.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)).filter r=
        (A.filter (fun a=>(if Sum.elim tail ktail a=v then Sum.elim head khead a else Sum.elim tail ktail a)∈T)).filter r:=by
      apply finite_filter_agree_on
      intro a _ h
      rcases hr a h with h|h
      · simp only [h,if_true]
        exact or_iff_right hz
      · by_cases ht:Sum.elim tail ktail a=v
        · simp [ht,h,hz]
        · simp [ht,h,hz]
    have hs (r:(V×U)→Prop) [DecidablePred r] (hr:∀ s,r s→s.1=v):
        (S.filter (fun s=>s.1∈T∨s.2∈W)).filter r=(S.filter (fun s=>s.2∈W)).filter r:=by
      apply finite_filter_agree_on
      intro s _ h
      rw [hr s h]
      exact or_iff_right hz
    have h0:=ha (fun a=>Sum.elim tail ktail a=v) (fun _ h=>Or.inl h)
    have h1:=ha (fun a=>Sum.elim head khead a=v) (fun _ h=>Or.inr h)
    have h2:=ha (fun a=>Sum.elim head khead a=v∧markedArcType a=true) (fun _ h=>Or.inr h.1)
    have h3:=hs (fun s=>s.1=v) (fun _ h=>h)
    have h4:=hs (fun s=>s.1=v∧HK s.1 s.2) (fun _ h=>h.1)
    dsimp only [markedFiniteDomainBalance]
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      simp only [h0,h1,h2,h3,h4]
  | inr u=>
    change u∉W at hz
    have hs (r:(V×U)→Prop) [DecidablePred r] (hr:∀ s,r s→s.2=u):
        (S.filter (fun s=>s.1∈T∨s.2∈W)).filter r=(S.filter (fun s=>s.1∈T)).filter r:=by
      apply finite_filter_agree_on
      intro s _ h
      rw [hr s h]
      exact or_iff_left hz
    have h0:=hs (fun s=>s.2=u∧¬HK s.1 s.2) (fun _ h=>h.1)
    have h1:=hs (fun s=>s.2=u∧HK s.1 s.2) (fun _ h=>h.1)
    dsimp only [markedFiniteDomainBalance]
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      simp only [h0,h1]

theorem markedFiniteBalance_star_inside
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (T:Finset V) (W:Finset U)
    (z:V⊕U) (hz:Sum.elim (fun v=>v∈T) (fun u=>u∈W) z) (i:Fin 4):
    markedFiniteBalance tail head ktail khead HK
      (A.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T))
      (S.filter (fun s=>s.1∈T∨s.2∈W)) m z i=
      markedFiniteBalance tail head ktail khead HK A S m z i:=by
  cases z with
  | inl v=>
    obtain ⟨h0,h1,h2,h3,h4⟩:=marked_star_restriction_row_counts (HK:=HK)
      (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) A S T W v hz
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      simp only [h0,h1,h2,h3,h4]
  | inr u=>
    obtain ⟨h1,h0⟩:=marked_star_restriction_hub_counts (HK:=HK) S T W u hz
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      simp only [h0,h1]

end Oberwolfach
