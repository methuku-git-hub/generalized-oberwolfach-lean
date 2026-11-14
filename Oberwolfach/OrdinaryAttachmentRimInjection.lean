module

public import Oberwolfach.OrdinaryExpansionAttachmentHom

@[expose] public section

/-! Identifying the distinguished vertex of each private wheel does not
identify rim edges. The original rim-pair encoding is explicitly injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E J W : Type*}

theorem attachmentCollapse_expansion_neighbor_injective
    (C : SimpleGraph W) (z o : W) (hzo : z≠o) (x y : E → V) (v : J → V)
    (i : E ⊕ J) (w : W) (a b : ExpansionRow V E J W)
    (ha : (ordinaryExpansionRim C z o x y).Adj a (.inr (i,w)))
    (hb : (ordinaryExpansionRim C z o x y).Adj b (.inr (i,w)))
    (heq : attachmentCollapse z (expansionAttachmentRoots x v) a=
      attachmentCollapse z (expansionAttachmentRoots x v) b) : a=b := by
  have hmix (a : V) (j : E ⊕ J) (t : W)
      (ha : (ordinaryExpansionRim C z o x y).Adj (.inl a) (.inr (i,w)))
      (hb : (ordinaryExpansionRim C z o x y).Adj (.inr (j,t)) (.inr (i,w)))
      (heq : attachmentCollapse z (expansionAttachmentRoots x v) (.inl a)=
        attachmentCollapse z (expansionAttachmentRoots x v) (.inr (j,t))) : False := by
    have ht := (attachmentWheelEmbedding_old z (expansionAttachmentRoots x v) j t a).mp heq.symm
    have htz := ht.1
    subst t
    obtain ⟨hji,hp⟩ := hb
    subst j
    cases i with
    | inr j => exact ha.elim
    | inl e =>
      rcases ha with ⟨_,hw⟩|⟨_,hw⟩
      · exact hp.2 (Or.inl ⟨rfl,hw⟩)
      · exact hp.1.ne hw.symm
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Sum.inl.inj heq)
    | inr p => exact (hmix a p.1 p.2 ha hb heq).elim
  | inr p =>
    cases b with
    | inl b => exact (hmix b p.1 p.2 hb ha heq.symm).elim
    | inr q =>
      rcases p with ⟨j,t⟩;rcases q with ⟨k,t'⟩
      obtain ⟨hji,_⟩ := ha;obtain ⟨hki,_⟩ := hb
      subst j;subst k
      have htt := (attachmentWheelEmbedding z (expansionAttachmentRoots x v) i).injective heq
      subst t'
      rfl

theorem attachmentCollapse_expansion_old_edge
    (C : SimpleGraph W) (z o : W) (hzo : z≠o) (x y : E → V) (v : J → V)
    (a b : ExpansionRow V E J W) (a₀ b₀ : V)
    (hab : (ordinaryExpansionRim C z o x y).Adj a b)
    (ha : attachmentCollapse z (expansionAttachmentRoots x v) a=.inl a₀)
    (hb : attachmentCollapse z (expansionAttachmentRoots x v) b=.inl b₀) :
    ∃ e,s(a,b)=s(Sum.inl (y e),Sum.inr (Sum.inl e,z)) := by
  have hcross (a : V) (i : E ⊕ J) (w : W) (b₀ : V)
      (hab : (ordinaryExpansionRim C z o x y).Adj (.inl a) (.inr (i,w)))
      (hb : attachmentCollapse z (expansionAttachmentRoots x v) (.inr (i,w))=.inl b₀) :
      ∃ e,s(Sum.inl a,Sum.inr (i,w))=s(Sum.inl (y e),Sum.inr (Sum.inl e,z)) := by
    have hw := ((attachmentWheelEmbedding_old z (expansionAttachmentRoots x v) i w b₀).mp hb).1
    subst w
    cases i with
    | inr j => exact hab.elim
    | inl e =>
      rcases hab with ⟨_,hz⟩|⟨ha,_⟩
      · exact (hzo hz).elim
      · subst a;exact ⟨e,rfl⟩
  cases a with
  | inl a =>
    cases b with
    | inl b => exact hab.elim
    | inr p => exact hcross a p.1 p.2 b₀ hab hb
  | inr p =>
    cases b with
    | inl b =>
      obtain ⟨e,he⟩ := hcross b p.1 p.2 a₀ hab ha
      exact ⟨e,(Sym2.eq_swap).trans he⟩
    | inr q =>
      rcases p with ⟨i,w⟩;rcases q with ⟨j,w'⟩
      have hw := ((attachmentWheelEmbedding_old z (expansionAttachmentRoots x v) i w a₀).mp ha).1
      have hw' := ((attachmentWheelEmbedding_old z (expansionAttachmentRoots x v) j w' b₀).mp hb).1
      exact (expansionPrivateAdj_adj C z o i w w' hab.2).ne (hw.trans hw'.symm) |>.elim

theorem ordinaryExpansion_attachment_rim_injective
    (C : SimpleGraph W) (z o : W) (hzo : z≠o) (x y : E → V) (v : J → V)
    (hxy : Function.Injective (fun e => s(x e,y e))) :
    Set.InjOn (Sym2.map (attachmentCollapse z (expansionAttachmentRoots x v)))
      (ordinaryExpansionRim C z o x y).edgeSet := by
  let q := attachmentCollapse z (expansionAttachmentRoots x v)
  have hordered (a b c d : ExpansionRow V E J W)
      (hab : (ordinaryExpansionRim C z o x y).Adj a b)
      (hcd : (ordinaryExpansionRim C z o x y).Adj c d)
      (hac : q a=q c) (hbd : q b=q d) : s(a,b)=s(c,d) := by
    cases hqa : q a with
    | inr p =>
      have ha := (attachmentCollapse_private_preimage z (expansionAttachmentRoots x v) a p.1 p.2).mp hqa
      have hc := (attachmentCollapse_private_preimage z (expansionAttachmentRoots x v) c p.1 p.2).mp (hac.symm.trans hqa)
      have hac' := ha.1.trans hc.1.symm
      subst c
      have hbd' := attachmentCollapse_expansion_neighbor_injective C z o hzo x y v p.1 p.2 b d
        (ha.1 ▸ hab.symm) (ha.1 ▸ hcd.symm) hbd
      subst d;rfl
    | inl a₀ =>
      cases hqb : q b with
      | inr p =>
        have hb := (attachmentCollapse_private_preimage z (expansionAttachmentRoots x v) b p.1 p.2).mp hqb
        have hd := (attachmentCollapse_private_preimage z (expansionAttachmentRoots x v) d p.1 p.2).mp (hbd.symm.trans hqb)
        have hbd' := hb.1.trans hd.1.symm
        subst d
        have hac' := attachmentCollapse_expansion_neighbor_injective C z o hzo x y v p.1 p.2 a c
          (hb.1 ▸ hab) (hb.1 ▸ hcd) hac
        subst c;rfl
      | inl b₀ =>
        obtain ⟨e,he⟩ := attachmentCollapse_expansion_old_edge C z o hzo x y v a b a₀ b₀ hab hqa hqb
        obtain ⟨e',he'⟩ := attachmentCollapse_expansion_old_edge C z o hzo x y v c d a₀ b₀ hcd
          (hac.symm.trans hqa) (hbd.symm.trans hqb)
        have hmap : Sym2.map q s(a,b)=Sym2.map q s(c,d) := by change s(q a,q b)=s(q c,q d);rw [hac,hbd]
        rw [he,he'] at hmap
        have hh : s(y e,x e)=s(y e',x e') := by
          apply Sym2.map.injective (f:=Sum.inl (β:=(E⊕J)×W)) Sum.inl_injective
          simpa [q,attachmentCollapse,attachmentWheelEmbedding,expansionAttachmentRoots] using hmap
        have hee : e=e' := hxy (by simpa only [Sym2.eq_swap] using hh)
        exact he.trans (hee ▸ he'.symm)
  intro e he e' he' hh
  induction e using Sym2.ind with
  | _ a b =>
    induction e' using Sym2.ind with
    | _ c d =>
      rcases Sym2.eq_iff.mp hh with ⟨hac,hbd⟩|⟨had,hbc⟩
      · exact hordered a b c d he he' hac hbd
      · exact (hordered a b d c he he'.symm had hbc).trans Sym2.eq_swap

end Oberwolfach
