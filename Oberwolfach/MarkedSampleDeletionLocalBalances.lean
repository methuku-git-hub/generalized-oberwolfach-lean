module

public import Oberwolfach.MarkedSampleDeletionIncidences
public import Oberwolfach.MarkedSampleHubClassSizes

@[expose] public section

/-! Transfer the three required local row balances to the actual sample
remaining after physical deletions. The input equalities concern explicit
finite sets of retained original occurrences and retained spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_physical_deletion_local_row_balances
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (v:V):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let src:=Sum.elim (fun e:E₀=>e.val.1) (fun e:E₁=>e.val.1)
    let dst:=Sum.elim (fun e:E₀=>e.val.2) (fun e:E₁=>e.val.2)
    let A:=Finset.univ.filter (fun a:E₀⊕E₁=>
      Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉DR.edgeFinset)
    let S:=Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧¬DS.Adj (Sum.inl z.1) (Sum.inr z.2))
    (A.filter (fun a=>dst a=v)).card=(A.filter (fun a=>src a=v)).card→
    (A.filter (fun a=>dst a=v)).card=(S.filter (fun z=>z.1=v)).card→
    (A.filter (fun a=>dst a=v∧markedArcType a=true)).card=
      (S.filter (fun z=>z.1=v∧H true z.1 z.2)).card→
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let src':=Sum.elim (fun e:E₀'=>e.val.1) (fun e:E₁'=>e.val.1)
    let dst':=Sum.elim (fun e:E₀'=>e.val.2) (fun e:E₁'=>e.val.2)
    (Finset.univ.filter (fun a=>dst' a=v)).card=(Finset.univ.filter (fun a=>src' a=v)).card ∧
    (Finset.univ.filter (fun a=>dst' a=v)).card=
      (Finset.univ.filter (fun z:V×U=>(H' false z.1 z.2∨H' true z.1 z.2)∧z.1=v)).card ∧
    (Finset.univ.filter (fun a=>dst' a=v∧markedArcType a=true)).card=
      (Finset.univ.filter (fun z:V×U=>H' true z.1 z.2∧z.1=v)).card:=by
  intro E₀ E₁ src dst A S hd hr hm
  dsimp only
  have hin:(Finset.univ.filter (fun a:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) false⊕
      MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) true=>
      Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a=v)).card=(A.filter (fun a=>dst a=v)).card:=by
    convert markedSampleDeletedArcsEmbedding_filter_card P π d σ DR.edgeFinset (fun a=>dst a=v) using 1
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases a <;> rfl
  have hout:(Finset.univ.filter (fun a:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) false⊕
      MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) true=>
      Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a=v)).card=(A.filter (fun a=>src a=v)).card:=by
    convert markedSampleDeletedArcsEmbedding_filter_card P π d σ DR.edgeFinset (fun a=>src a=v) using 1
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases a <;> rfl
  have hmarked:(Finset.univ.filter (fun a:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) false⊕
      MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) true=>
      Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a=v∧markedArcType a=true)).card=
      (A.filter (fun a=>dst a=v∧markedArcType a=true)).card:=by
    convert markedSampleDeletedArcsEmbedding_filter_card P π d σ DR.edgeFinset (fun a=>dst a=v∧markedArcType a=true) using 1
    · congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases a <;> rfl
    · congr 1
      ext a
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      cases a <;> rfl
  have hs:Finset.univ.filter (fun z:V×U=>(markedDeletePhysicalSpokes H DS false z.1 z.2∨
      markedDeletePhysicalSpokes H DS true z.1 z.2)∧z.1=v)=S.filter (fun z=>z.1=v):=by
    ext z
    simp only [S,markedDeletePhysicalSpokes,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  have hsk:Finset.univ.filter (fun z:V×U=>markedDeletePhysicalSpokes H DS true z.1 z.2∧z.1=v)=
      S.filter (fun z=>z.1=v∧H true z.1 z.2):=by
    ext z
    simp only [S,markedDeletePhysicalSpokes,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  rw [hin,hout,hmarked,hs,hsk]
  exact ⟨hd,hr,hm⟩

theorem marked_sample_physical_deletion_local_hub_balance
    (H:Bool→V→U→Prop) (DS:SimpleGraph (V⊕U)) (u:U) (m:ℕ)
    (hH:∀ x,¬(H false x u∧H true x u)):
    let S:=Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧¬DS.Adj (Sum.inl z.1) (Sum.inr z.2))
    (S.filter (fun z=>z.2=u∧¬H true z.1 z.2)).card=m*(S.filter (fun z=>z.2=u∧H true z.1 z.2)).card→
    Fintype.card (hubNeighbourClass (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true) u false)=
      m*Fintype.card (hubNeighbourClass (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true) u true):=by
  intro S hh
  have hS:∀ z∈S,H false z.1 z.2∨H true z.1 z.2:=by intro z hz;exact (Finset.mem_filter.mp hz).2.1
  have h:=marked_finite_host_local_hub_balance (H false) (H true) m S hS u hH hh
  have he (b:Bool):Finset.univ.filter (fun x=>H b x u∧(x,u)∈S)=
      Finset.univ.filter (markedDeletePhysicalSpokes H DS b · u):=by
    ext x
    simp only [S,markedDeletePhysicalSpokes,Finset.mem_filter,Finset.mem_univ,true_and]
    cases b <;> tauto
  rw [he,he] at h
  simpa only [hubNeighbourClass,Bool.false_eq_true,ite_false,ite_true,Fintype.card_subtype] using h

end Oberwolfach
