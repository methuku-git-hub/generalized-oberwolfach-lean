module

public import Oberwolfach.MarkedFiniteStarBalance
public import Oberwolfach.MarkedFiniteDomainBalanceBounds

@[expose] public section

/-! At roots in an induced pair, restricting the opposite endpoint to
smaller contained domains gives the original ambient balance. A sparse
inner correction costs only its actual incidence bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteDomainBalance_induced_inside
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ)
    (I T:Finset V) (J W:Finset U) (hT:T⊆I) (hW:W⊆J)
    (z:V⊕U) (hz:Sum.elim (fun v=>v∈I) (fun u=>u∈J) z) (i:Fin 4):
    markedFiniteDomainBalance tail head ktail khead HK
      (A.filter (fun a=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))
      (S.filter (fun s=>s.1∈I∧s.2∈J)) m T W z i=
      markedFiniteDomainBalance tail head ktail khead HK A S m T W z i:=by
  cases z with
  | inl v=>
    change v∈I at hz
    have ha (r:(E⊕K)→Prop) [DecidablePred r]
        (hr:∀ a,r a→Sum.elim tail ktail a=v∨Sum.elim head khead a=v):
        (((A.filter (fun a=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)).filter
          (fun a=>(if Sum.elim tail ktail a=v then Sum.elim head khead a else Sum.elim tail ktail a)∈T)).filter r)=
        (A.filter (fun a=>(if Sum.elim tail ktail a=v then Sum.elim head khead a else Sum.elim tail ktail a)∈T)).filter r:=by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · tauto
      · rintro ⟨⟨ha,hopp⟩,hr'⟩
        have hb:Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I:=by
          rcases hr a hr' with ht|hh
          · simp only [ht,ite_true] at hopp
            exact ⟨ht.symm ▸ hz,hT hopp⟩
          · by_cases ht:Sum.elim tail ktail a=v
            · exact ⟨ht.symm ▸ hz,hh.symm ▸ hz⟩
            · simp only [ht,ite_false] at hopp
              exact ⟨hT hopp,hh.symm ▸ hz⟩
        exact ⟨⟨⟨ha,hb⟩,hopp⟩,hr'⟩
    have hs (r:(V×U)→Prop) [DecidablePred r] (hr:∀ s,r s→s.1=v):
        (((S.filter (fun s=>s.1∈I∧s.2∈J)).filter (fun s=>s.2∈W)).filter r)=
        (S.filter (fun s=>s.2∈W)).filter r:=by
      ext s;simp only [Finset.mem_filter]
      constructor
      · tauto
      · rintro ⟨⟨hs,hw⟩,hr'⟩
        exact ⟨⟨⟨hs,(hr s hr').symm ▸ hz,hW hw⟩,hw⟩,hr'⟩
    have h0:=ha (fun a=>Sum.elim tail ktail a=v) (fun _ h=>Or.inl h)
    have h1:=ha (fun a=>Sum.elim head khead a=v) (fun _ h=>Or.inr h)
    have h2:=ha (fun a=>Sum.elim head khead a=v∧markedArcType a=true) (fun _ h=>Or.inr h.1)
    have h3:=hs (fun s=>s.1=v) (fun _ h=>h)
    have h4:=hs (fun s=>s.1=v∧HK s.1 s.2) (fun _ h=>h.1)
    dsimp only [markedFiniteDomainBalance]
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      simp only [h0,h1,h2,h3,h4]
  | inr u=>
    change u∈J at hz
    have hs (r:(V×U)→Prop) [DecidablePred r] (hr:∀ s,r s→s.2=u):
        (((S.filter (fun s=>s.1∈I∧s.2∈J)).filter (fun s=>s.1∈T)).filter r)=
        (S.filter (fun s=>s.1∈T)).filter r:=by
      ext s;simp only [Finset.mem_filter]
      constructor
      · tauto
      · rintro ⟨⟨hs,ht⟩,hr'⟩
        exact ⟨⟨⟨hs,hT ht,(hr s hr').symm ▸ hz⟩,ht⟩,hr'⟩
    have h0:=hs (fun s=>s.2=u∧¬HK s.1 s.2) (fun _ h=>h.1)
    have h1:=hs (fun s=>s.2=u∧HK s.1 s.2) (fun _ h=>h.1)
    dsimp only [markedFiniteDomainBalance]
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      simp only [h0,h1]

end Oberwolfach
