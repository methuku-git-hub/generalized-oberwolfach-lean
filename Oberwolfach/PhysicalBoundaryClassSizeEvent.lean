module

public import Oberwolfach.RetainedCoinCountsCommonEvent
public import Oberwolfach.MarkedBoundaryEndpointSampling

@[expose] public section

/-! All fixed endpoint, spoke-row and spoke-column class sizes concentrate
on one original physical sampling event. No independence between different
classes is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_image_class_card {A E:Type} [DecidableEq A] [DecidableEq E]
    (f:A↪E) (S:Finset A) (σ:E→Bool):
    ((S.image f).filter (fun e=>σ e=true)).card=(S.filter (fun a=>σ (f a)=true)).card:=by
  rw [Finset.filter_image,Finset.card_image_of_injective _ f.injective]

theorem physical_boundary_class_size_event (ε:ℝ) (hε:0<ε) (q:ℕ):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
    N≤Fintype.card (V⊕U)→∀ (π:Equiv.Perm V)
      (L:Bool→Bool→V→Finset V) (B:Bool→V→Finset U) (T:U→Finset V)
      (p:ℝ) (hp:0≤p) (hp1:p≤1),
    1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp hp1)).probability (fun σ=>
      (∀ mark incoming x,
        |(((L mark incoming x).filter (fun v=>σ (markedBoundaryEndpointCoin π mark incoming x (Sum.inl v))=true)).card:ℝ)-
          p*(L mark incoming x).card|≤ε*Fintype.card (V⊕U))∧
      (∀ b x,|(((B b x).filter (fun u=>σ s(Sum.inl x,Sum.inr u)=true)).card:ℝ)-p*(B b x).card|≤ε*Fintype.card (V⊕U))∧
      (∀ u,|(((T u).filter (fun x=>σ s(Sum.inl x,Sum.inr u)=true)).card:ℝ)-p*(T u).card|≤ε*Fintype.card (V⊕U))):=by
  obtain ⟨N,hN⟩:=retained_coin_counts_common_event 7 1 ε (by norm_num) hε 1 q
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn π L B T p hp hp1
  let J:Type:=(Bool×Bool×V)⊕((Bool×V)⊕U)
  let fL:Bool→Bool→V→V↪Sym2 (V⊕U):=fun mark incoming x=>
    (Function.Embedding.inl).trans (markedBoundaryEndpointCoin π mark incoming x)
  let fB:V→U↪Sym2 (V⊕U):=fun x=>
    (Function.Embedding.inr).trans (markedBoundaryEndpointCoin π false false x)
  let fT:U→V↪Sym2 (V⊕U):=fun u=>⟨fun x=>s(Sum.inl x,Sum.inr u),by
    intro x y he
    rcases Sym2.eq_iff.mp he with ⟨h,_⟩|⟨h,_⟩
    · exact Sum.inl.inj h
    · exact (Sum.inl_ne_inr h).elim⟩
  let A:J→Finset (Sym2 (V⊕U)):=fun j=>match j with
    | Sum.inl (mark,incoming,x)=>(L mark incoming x).image (fL mark incoming x)
    | Sum.inr (Sum.inl (b,x))=>(B b x).image (fB x)
    | Sum.inr (Sum.inr u)=>(T u).image (fT u)
  have hcount:(Fintype.card J:ℝ)≤7*(Fintype.card (V⊕U):ℝ)^1:=by
    simp only [J,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,pow_one]
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V),Nat.cast_nonneg (α:=ℝ) (Fintype.card U)]
  have hsize (j:J):((A j).card:ℝ)≤1*Fintype.card (V⊕U):=by
    have hnat:(A j).card≤Fintype.card (V⊕U):=by
      rcases j with ⟨mark,incoming,x⟩|⟨b,x⟩|u
      · exact (Finset.card_image_le.trans (Finset.card_le_univ _)).trans (by simp [Fintype.card_sum])
      · exact (Finset.card_image_le.trans (Finset.card_le_univ _)).trans (by simp [Fintype.card_sum])
      · exact (Finset.card_image_le.trans (Finset.card_le_univ _)).trans (by simp [Fintype.card_sum])
    simpa only [one_mul] using (show ((A j).card:ℝ)≤(Fintype.card (V⊕U):ℝ) from Nat.cast_le.mpr hnat)
  have hevent:=hN (Fintype.card (V⊕U)) hn (Sym2 (V⊕U)) J hcount A hsize p hp hp1
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  refine ⟨?_,?_,?_⟩
  · intro mark incoming x
    have h:=(hσ (Sum.inl (mark,incoming,x))).le
    dsimp only [A] at h
    rw [retained_image_class_card,Finset.card_image_of_injective _ (fL mark incoming x).injective] at h
    exact h
  · intro b x
    have h:=(hσ (Sum.inr (Sum.inl (b,x)))).le
    dsimp only [A] at h
    rw [retained_image_class_card,Finset.card_image_of_injective _ (fB x).injective] at h
    exact h
  · intro u
    have h:=(hσ (Sum.inr (Sum.inr u))).le
    dsimp only [A] at h
    rw [retained_image_class_card,Finset.card_image_of_injective _ (fT u).injective] at h
    exact h
end Oberwolfach
