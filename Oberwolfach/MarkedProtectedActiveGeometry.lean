module

public import Oberwolfach.MarkedActiveInnerParentDegrees
public import Oberwolfach.InvariantPermutation

@[expose] public section

/-! Actual inner and ambient orders after removing the protected rows and
hubs. Both lower bounds refer to the same active ambient order. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A W U B:Type} [Fintype V] [Fintype A] [Fintype W] [Fintype U] [Fintype B]
  [DecidableEq V] [DecidableEq A] [DecidableEq U] [DecidableEq B]

theorem marked_protected_active_geometry
    (f:A↪V) (g:B↪U) (i:W↪A) (I T:Finset V) (J Z:Finset U) (XA:Finset A) (ZA:Finset B)
    (hf:Finset.univ.image f=Finset.univ\T) (hg:Finset.univ.image g=Finset.univ\Z)
    (hi:Finset.univ.image i=XA) (hXA:XA.image f=I\T) (hZA:ZA.image g=J\Z)
    (hU:Fintype.card U≤Fintype.card V)
    (iota omegaI xi:ℝ) (hiota:0< iota) (hOmega:0<omegaI) (hOmega1:omegaI≤1) (hxi:0≤xi)
    (hIlow:iota*Fintype.card V≤(I.card:ℝ)) (hJlow:omegaI*I.card≤(J.card:ℝ))
    (hIup:(I.card:ℝ)≤(xi/4)*Fintype.card V) (hJup:J.card≤I.card)
    (hTsize:(T.card:ℝ)≤(iota/2)*Fintype.card V)
    (hZsize:(Z.card:ℝ)≤(omegaI*iota/2)*Fintype.card V)
    (hThalf:(T.card:ℝ)≤(Fintype.card V:ℝ)/2):
    (Fintype.card V:ℝ)/2≤Fintype.card A∧
    (Fintype.card (A⊕B):ℝ)≤2*Fintype.card V∧
    (iota/2)*Fintype.card V≤(Fintype.card W:ℝ)∧
    (omegaI*iota/2)*Fintype.card V≤(ZA.card:ℝ)∧
    (omegaI*iota/4)*Fintype.card (A⊕B)≤(Fintype.card W:ℝ)∧
    (omegaI*iota/4)*Fintype.card (A⊕B)≤(ZA.card:ℝ)∧
    ((ordinaryInnerVertices XA ZA).card:ℝ)≤xi*Fintype.card A:=by
  have hcA:Fintype.card A=(Finset.univ\T).card:=by
    rw [←hf,Finset.card_image_of_injective _ f.injective,Finset.card_univ]
  have hcW:Fintype.card W=(I\T).card:=by
    rw [←hXA,Finset.card_image_of_injective _ f.injective,←hi,Finset.card_image_of_injective _ i.injective,Finset.card_univ]
  have hcZ:ZA.card=(J\Z).card:=by
    rw [←hZA,Finset.card_image_of_injective _ g.injective]
  have hAlow:(Fintype.card V:ℝ)/2≤Fintype.card A:=by
    have hh:=Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
    rw [Finset.card_univ,←hcA] at hh
    have hh':(Fintype.card A:ℝ)+T.card=Fintype.card V:=by exact_mod_cast hh
    linarith only [hh',hThalf]
  have hAmbient:(Fintype.card (A⊕B):ℝ)≤2*Fintype.card V:=by
    have ha:=Fintype.card_le_of_injective f f.injective
    have hb:=Fintype.card_le_of_injective g g.injective
    simp only [Fintype.card_sum,Nat.cast_add]
    exact_mod_cast (show Fintype.card A+Fintype.card B≤2*Fintype.card V by omega)
  have hsplitI:(I.card:ℝ)≤Fintype.card W+T.card:=by
    have h:=Finset.card_sdiff_add_card_inter I T
    have hle: (I∩T).card≤T.card:=Finset.card_le_card Finset.inter_subset_right
    rw [←hcW] at h
    exact_mod_cast (show I.card≤Fintype.card W+T.card by omega)
  have hsplitJ:(J.card:ℝ)≤ZA.card+Z.card:=by
    have h:=Finset.card_sdiff_add_card_inter J Z
    have hle:(J∩Z).card≤Z.card:=Finset.card_le_card Finset.inter_subset_right
    rw [←hcZ] at h
    exact_mod_cast (show J.card≤ZA.card+Z.card by omega)
  have hW:(iota/2)*Fintype.card V≤(Fintype.card W:ℝ):=by
    linarith only [hIlow,hsplitI,hTsize]
  have hZ:(omegaI*iota/2)*Fintype.card V≤(ZA.card:ℝ):=by
    have hh:=mul_le_mul_of_nonneg_left hIlow hOmega.le
    nlinarith only [hh,hJlow,hsplitJ,hZsize]
  have hscale:=mul_le_mul_of_nonneg_left hAmbient (show 0≤omegaI*iota/4 by positivity)
  have hOm:=mul_le_mul_of_nonneg_right hOmega1 (show 0≤ iota*Fintype.card V by positivity)
  refine ⟨hAlow,hAmbient,hW,hZ,by nlinarith only [hscale,hW,hOm],by nlinarith only [hscale,hZ],?_⟩
  have hXAcard:XA.card=(I\T).card:=by rw [←hXA,Finset.card_image_of_injective _ f.injective]
  have hXAup:(XA.card:ℝ)≤I.card:=by rw [hXAcard];exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : I\T⊆I)
  have hZAup:(ZA.card:ℝ)≤I.card:=by
    rw [hcZ];exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : J\Z⊆J)).trans hJup
  have hInner:((ordinaryInnerVertices XA ZA).card:ℝ)=XA.card+ZA.card:=by
    have hd:Disjoint (XA.image (Sum.inl:A→A⊕B)) (ZA.image Sum.inr):=by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hz
      obtain ⟨y,_,he⟩:=Finset.mem_image.mp hz'
      exact Sum.inr_ne_inl he
    rw [ordinaryInnerVertices,Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective,Nat.cast_add]
  have hscale':=mul_le_mul_of_nonneg_left hAlow hxi
  rw [hInner]
  nlinarith only [hXAup,hZAup,hIup,hscale']

end Oberwolfach
