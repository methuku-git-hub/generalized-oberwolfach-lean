module

public import Oberwolfach.MarkedDeepHostBalanceTransport

@[expose] public section
/-! Enumerate the small root sets in the form required by the sampled
row-and-hub cover theorem, retaining all typed balance conditions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
omit [Fintype Γ] [Fintype Color] in
theorem marked_deep_host_enumerate_roots
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (I T:Finset V) (J W:Finset U) (hTI:T⊆I) (hWJ:W⊆J)
    (hdis:∀ x u,¬(H false x u∧H true x u))
    (hshift:∀ u x z,H false x u→H true z u→x≠π z)
    (hb:MarkedDeepHostBalanced P π d m σ H I T J W):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let src:=Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1)
    let dst:=Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2)
    let F:=Iᶜ;
    ∃ (u:Fin W.card→U) (v:Fin T.card→V),
      Function.Injective u∧Function.Injective v∧Finset.univ.image u=W∧Finset.univ.image v=T∧
      (∀ i x,¬(H false x (u i)∧H true x (u i)))∧
      (∀ i x z,H false x (u i)→H true z (u i)→x≠π z)∧
      (∀ i,Fintype.card (hubNeighbourClass (H false) (H true) (u i) false)=
        m*Fintype.card (hubNeighbourClass (H false) (H true) (u i) true))∧
      (∀ i x,H false x (u i)∨H true x (u i)→x∈F)∧
      (∀ i,v i∉F)∧(∀ i z,¬(H false (v i) z∧H true (v i) z))∧
      (∀ i,∀ a:E⊕K,dst a=v i→src a∈F)∧
      (∀ i,∀ a:E⊕K,src a=v i→dst a∈F)∧
      (∀ i,(Finset.univ.filter (fun a:E⊕K=>dst a=v i)).card=
        (Finset.univ.filter (fun a:E⊕K=>src a=v i)).card)∧
      (∀ i,(Finset.univ.filter (fun a:E⊕K=>dst a=v i)).card=
        (Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧z.1=v i)).card)∧
      (∀ i,(Finset.univ.filter (fun a:E⊕K=>dst a=v i∧markedArcType a=true)).card=
        (Finset.univ.filter (fun z:V×U=>H true z.1 z.2∧z.1=v i)).card)∧
      (∀ i,Disjoint ((Finset.univ.filter (H false (v i)))∪(Finset.univ.filter (H true (v i))))
        (Finset.univ.image u)):=by
  intro E K src dst F
  obtain ⟨hbal,hratio,hinc,hout,hrowSupport,hhubSupport⟩:=hb
  let eu:Fin W.card≃W:=(Fintype.equivFinOfCardEq (Fintype.card_coe W)).symm
  let ev:Fin T.card≃T:=(Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  let u:Fin W.card→U:=fun i=>(eu i).val
  let v:Fin T.card→V:=fun i=>(ev i).val
  have hu:Function.Injective u:=fun i j h=>eu.injective (Subtype.ext h)
  have hv:Function.Injective v:=fun i j h=>ev.injective (Subtype.ext h)
  have huW (i):u i∈W:=(eu i).property
  have hvT (i):v i∈T:=(ev i).property
  have huimage:Finset.univ.image u=W:=by
    ext z
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩;exact huW i
    · intro hz
      obtain ⟨i,hi⟩:=eu.surjective ⟨z,hz⟩
      exact ⟨i,by simp only [u,hi]⟩
  have hvimage:Finset.univ.image v=T:=by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩;exact hvT i
    · intro hx
      obtain ⟨i,hi⟩:=ev.surjective ⟨x,hx⟩
      exact ⟨i,by simp only [v,hi]⟩
  refine ⟨u,v,hu,hv,huimage,hvimage,(fun i x=>hdis x (u i)),
    (fun i x z=>hshift (u i) x z),(fun i=>hratio (u i) (huW i)),
    (fun i x hx=>Finset.mem_compl.mpr (hhubSupport (u i) (huW i) x hx)),
    (fun i=>by change v i∉Iᶜ; simpa only [Finset.mem_compl,not_not] using hTI (hvT i)),
    (fun i z=>hdis (v i) z),
    (fun i a ha=>by
      apply Finset.mem_compl.mpr
      apply hinc a
      change dst a∈T
      rw [ha]
      exact hvT i),
    (fun i a ha=>by
      apply Finset.mem_compl.mpr
      apply hout a
      change src a∈T
      rw [ha]
      exact hvT i),
    (fun i=>(hbal (v i) (hvT i)).1), (fun i=>(hbal (v i) (hvT i)).2.1),
    (fun i=>(hbal (v i) (hvT i)).2.2),?_⟩
  intro i
  rw [huimage]
  apply Finset.disjoint_left.mpr
  intro z hz hzW
  have hs:H false (v i) z∨H true (v i) z:=by
    simpa only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] using hz
  exact hrowSupport (v i) (hvT i) z hs (hWJ hzW)
end Oberwolfach
