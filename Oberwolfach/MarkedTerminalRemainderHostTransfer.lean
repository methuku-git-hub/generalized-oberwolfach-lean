module

public import Oberwolfach.MarkedDecompositionHostTransfer
public import Oberwolfach.MarkedFiniteRemainderTransfer

@[expose] public section

/-! Absorb a finite remainder from a different completion host. Its actual
arc identifiers are embedded in the sampled terminal host, preserving
endpoints and types; physical injectivity proves that no multiplicity is
lost. Transfer back uses agreement only on the absorber and remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [DecidableEq V] [DecidableEq U]
  [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V} {ktail' khead':K'→V}
  {m b:ℕ} {π:Equiv.Perm V} {H₀ HK H₀' HK':V→U→Prop}

theorem marked_terminal_remainder_absorption_between_hosts
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hp':Function.Injective (markedPhysicalEdge tail' head' ktail' khead' π))
    (A₀:Finset (E⊕K)) (A:Finset (E'⊕K')) (S:Finset (V×U)) (C:Finset (Finset V⊕(V×U)))
    (habs:∀ B⊆A₀,MarkedRemainderDivisible tail head ktail khead HK B S m→
      IsResourceAbsorber
        (fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W)
        (B.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr) C)
    (hdiv:MarkedRemainderDivisible tail' head' ktail' khead' HK' A S m)
    (hA:∀ a∈A,∃ a₀∈A₀,Sum.elim tail ktail a₀=Sum.elim tail' ktail' a∧
      Sum.elim head khead a₀=Sum.elim head' khead' a∧markedArcType a₀=markedArcType a)
    (hS:∀ z∈S,(H₀ z.1 z.2↔H₀' z.1 z.2)∧(HK z.1 z.2↔HK' z.1 z.2))
    (hCE:∀ e:E,Sum.inl ({tail e,head e}:Finset V)∈C→∃ e':E',tail' e'=tail e∧head' e'=head e)
    (hCK:∀ e:K,Sum.inl ({ktail e,π (khead e)}:Finset V)∈C→∃ e':K',ktail' e'=ktail e∧khead' e'=khead e)
    (hC₀:∀ v u,Sum.inr (v,u)∈C→H₀ v u→H₀' v u)
    (hCk:∀ v u,Sum.inr (v,u)∈C→HK v u→HK' v u):
    IsResourceAbsorber
      (fun W:MarkedWheel tail' head' ktail' khead' m π b H₀' HK'=>markedWheelPhysicalResources W)
      (A.image (fun a=>Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a))∪S.image Sum.inr) C:=by
  have hex (a:A):∃ a₀∈A₀,Sum.elim tail ktail a₀=Sum.elim tail' ktail' a.val∧
      Sum.elim head khead a₀=Sum.elim head' khead' a.val∧markedArcType a₀=markedArcType a.val:=hA a.val a.property
  choose f hf hs hd ht using hex
  have hfinj:=marked_finite_remainder_map_injective π hp' A f hs hd ht
  let B:=Finset.univ.image f
  have hB:B⊆A₀:=by
    intro a ha
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp ha
    exact hf j
  have hdivB:MarkedRemainderDivisible tail head ktail khead HK B S m:=
    marked_finite_remainder_image_divisible A S f hfinj hs hd ht (fun z hz=>(hS z hz).2) hdiv
  have hBabs:=habs B hB hdivB
  let L:=B.image (fun a=>Sum.inl (β:=V×U) (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr
  have hpre (a:E⊕K) (ha:Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈L):∃ j:A,f j=a:=by
    rcases Finset.mem_union.mp ha with ha|ha
    · obtain ⟨a',ha',heq⟩:=Finset.mem_image.mp ha
      have heq':a'=a:=hp (Sum.inl.inj heq)
      obtain ⟨j,_,hj⟩:=Finset.mem_image.mp ha'
      exact ⟨j,hj.trans heq'⟩
    · obtain ⟨z,_,hz⟩:=Finset.mem_image.mp ha
      exact (Sum.inr_ne_inl hz).elim
  have hsp (z:V×U) (hz:Sum.inr z∈L):z∈S:=by
    rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hz
      exact (Sum.inl_ne_inr ha).elim
    · obtain ⟨z',hz',heq⟩:=Finset.mem_image.mp hz
      exact Sum.inr.inj heq ▸ hz'
  have hE:∀ e:E,Sum.inl ({tail e,head e}:Finset V)∈C∪L→∃ e':E',tail' e'=tail e∧head' e'=head e:=by
    intro e he
    rcases Finset.mem_union.mp he with hc|hl
    · exact hCE e hc
    · obtain ⟨j,hj⟩:=hpre (Sum.inl e) hl
      have htt:=ht j
      cases hx:j.val with
      | inl er=>
        refine ⟨er,?_,?_⟩
        · simpa only [hj,hx,Sum.elim_inl] using (hs j).symm
        · simpa only [hj,hx,Sum.elim_inl] using (hd j).symm
      | inr er=>simp only [hj,hx,markedArcType,Bool.false_eq_true] at htt
  have hK:∀ e:K,Sum.inl ({ktail e,π (khead e)}:Finset V)∈C∪L→∃ e':K',ktail' e'=ktail e∧khead' e'=khead e:=by
    intro e he
    rcases Finset.mem_union.mp he with hc|hl
    · exact hCK e hc
    · obtain ⟨j,hj⟩:=hpre (Sum.inr e) hl
      have htt:=ht j
      cases hx:j.val with
      | inl er=>simp only [hj,hx,markedArcType,Bool.true_eq_false] at htt
      | inr er=>
        refine ⟨er,?_,?_⟩
        · simpa only [hj,hx,Sum.elim_inr] using (hs j).symm
        · simpa only [hj,hx,Sum.elim_inr] using (hd j).symm
  have h₀:∀ v u,Sum.inr (v,u)∈C∪L→H₀ v u→H₀' v u:=by
    intro v u he hh
    rcases Finset.mem_union.mp he with hc|hl
    · exact hC₀ v u hc hh
    · exact (hS (v,u) (hsp (v,u) hl)).1.mp hh
  have hk:∀ v u,Sum.inr (v,u)∈C∪L→HK v u→HK' v u:=by
    intro v u he hh
    rcases Finset.mem_union.mp he with hc|hl
    · exact hCk v u hc hh
    · exact (hS (v,u) (hsp (v,u) hl)).2.mp hh
  have hout:=marked_absorber_transfer_on_resources C L hE hK h₀ hk hBabs
  have heq:=marked_finite_remainder_image_resources π A S f hs hd ht
  change L=_ at heq
  rwa [heq] at hout

end Oberwolfach
