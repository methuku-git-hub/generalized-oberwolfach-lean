module

public import Oberwolfach.MarkedFiniteStarBalance

@[expose] public section

/-! The temporary reserved star contributes no restricted balance on
the active inner pair, at any active row or hub. The opposite-endpoint
restriction and the exclusion of the deeper roots are both explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteDomainBalance_star_active_zero
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ)
    (X T:Finset V) (Z W:Finset U)
    (z:V⊕U) (hz:Sum.elim (fun v=>v∉T) (fun u=>u∉W) z) (i:Fin 4):
    markedFiniteDomainBalance tail head ktail khead HK
      (A.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T))
      (S.filter (fun s=>s.1∈T∨s.2∈W)) m (X\T) (Z\W) z i=0:=by
  cases z with
  | inl v=>
    change v∉T at hz
    have ha (r:(E⊕K)→Prop) [DecidablePred r]
        (hr:∀ a,r a→Sum.elim tail ktail a=v∨Sum.elim head khead a=v):
        (((A.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)).filter
          (fun a=>(if Sum.elim tail ktail a=v then Sum.elim head khead a else Sum.elim tail ktail a)∈X\T)).filter r)=∅:=by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha hr'
      obtain ⟨ha,hactive⟩:=Finset.mem_filter.mp ha
      obtain ⟨_,hstar⟩:=Finset.mem_filter.mp ha
      rcases hr a hr' with ht|hh
      · simp only [ht,ite_true,Finset.mem_sdiff] at hactive
        rcases hstar with hstar|hstar
        · exact hz (ht ▸ hstar)
        · exact hactive.2 hstar
      · by_cases ht:Sum.elim tail ktail a=v
        · rcases hstar with h|h
          · exact hz (ht ▸ h)
          · exact hz (hh ▸ h)
        · simp only [ht,ite_false,Finset.mem_sdiff] at hactive
          rcases hstar with hstar|hstar
          · exact hactive.2 hstar
          · exact hz (hh ▸ hstar)
    have hs (r:(V×U)→Prop) [DecidablePred r] (hr:∀ s,r s→s.1=v):
        (((S.filter (fun s=>s.1∈T∨s.2∈W)).filter (fun s=>s.2∈Z\W)).filter r)=∅:=by
      apply Finset.filter_eq_empty_iff.mpr
      intro s hs hr'
      obtain ⟨hs,hactive⟩:=Finset.mem_filter.mp hs
      obtain ⟨_,hstar⟩:=Finset.mem_filter.mp hs
      rcases hstar with h|h
      · exact hz (hr s hr' ▸ h)
      · exact (Finset.mem_sdiff.mp hactive).2 h
    have h0:=ha (fun a=>Sum.elim tail ktail a=v) (fun _ h=>Or.inl h)
    have h1:=ha (fun a=>Sum.elim head khead a=v) (fun _ h=>Or.inr h)
    have h2:=ha (fun a=>Sum.elim head khead a=v∧markedArcType a=true) (fun _ h=>Or.inr h.1)
    have h3:=hs (fun s=>s.1=v) (fun _ h=>h)
    have h4:=hs (fun s=>s.1=v∧HK s.1 s.2) (fun _ h=>h.1)
    dsimp only [markedFiniteDomainBalance]
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      simp only [h0,h1,h2,h3,h4,Finset.card_empty,Nat.cast_zero,sub_zero]
  | inr u=>
    change u∉W at hz
    have hs (r:(V×U)→Prop) [DecidablePred r] (hr:∀ s,r s→s.2=u):
        (((S.filter (fun s=>s.1∈T∨s.2∈W)).filter (fun s=>s.1∈X\T)).filter r)=∅:=by
      apply Finset.filter_eq_empty_iff.mpr
      intro s hs hr'
      obtain ⟨hs,hactive⟩:=Finset.mem_filter.mp hs
      obtain ⟨_,hstar⟩:=Finset.mem_filter.mp hs
      rcases hstar with h|h
      · exact (Finset.mem_sdiff.mp hactive).2 h
      · exact hz (hr s hr' ▸ h)
    have h0:=hs (fun s=>s.2=u∧¬HK s.1 s.2) (fun _ h=>h.1)
    have h1:=hs (fun s=>s.2=u∧HK s.1 s.2) (fun _ h=>h.1)
    dsimp only [markedFiniteDomainBalance]
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      simp only [h0,h1,Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero]

end Oberwolfach
