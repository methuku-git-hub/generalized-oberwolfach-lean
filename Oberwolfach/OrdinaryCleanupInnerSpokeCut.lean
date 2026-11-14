module

public import Oberwolfach.OrdinaryCleanupSpokeCodegrees
public import Oberwolfach.OrdinaryCleanupSpokeColumns
public import Oberwolfach.FiniteCodegreeLargeCut
public import Oberwolfach.DomainCodegreeCuts

@[expose] public section
/-! The inner spoke cut needed by sparse correction follows from the same
    sampled cleanup profile and explicit quantitative margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_inner_spoke_cut
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (B:Finset U)
    (pR pH density tR tH L βe βh ε ζ δ h:ℝ) (Dmax:ℕ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d I B pR pH density tR tH L βe βh s j raw)
    (hI:0<I.card) (hB:0<B.card) (hp:0<pH) (hp1:pH≤1)
    (hε:0≤ε) (hζ:0≤ζ) (hδ:δ≤pH/16) (hζsmall:ζ≤pH^2/128) (hh:2*h≤pH/8)
    (hL:0≤L) (hF:∀v,F.degree v≤Dmax)
    (herror:tH+2*L≤ε*B.card)
    (hrowMin:tH+L≤pH*B.card/2) (hcolMin:tR+L≤pH*I.card/2)
    (hbudget:3*ε*(I.card:ℝ)^2*(B.card:ℝ)^2+
      ((Dmax+1:ℕ):ℝ)*I.card*(B.card:ℝ)^2≤(ζ*I.card*B.card)^2):
    BipartiteLargeCut (relationMultiplicity (fun v:I=>fun u:B=>H v.val u.val)) δ (2*h):=by
  let φ:I↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let Hloc:=fun v:I=>fun u:B=>H v.val u.val
  let F':=F.comap φ
  let E:=fun v:I=>insert v (F'.neighborFinset v)
  have hE (v:I):((E v).card:ℝ)≤(Dmax+1:ℕ):=by
    have hd:(F'.degree v)≤Dmax:=by
      exact (embedding_comap_degree_le φ F v).trans (hF v.val)
    have he:(E v).card≤Dmax+1:=by
      have hh:=Finset.card_insert_le v (F'.neighborFinset v)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hh
      exact hh.trans (Nat.add_le_add_right hd 1)
    exact_mod_cast he
  have hcounts:=ordinary_cleanup_spoke_degrees_and_codegrees P Q F H π d I B pR pH density tR tH L βe βh s j raw profile
  have hcolumns:=ordinary_cleanup_spoke_column_degrees P Q F H π d I B pR pH density tR tH L βe βh s j raw profile
  have hrow (v:I):(pH-ε)*Fintype.card B≤∑u,bipAdj Hloc v u:=by
    have he:(∑u:B,bipAdj Hloc v u)=(B.filter (H v.val)).card:=finite_domain_indicator_sum B (H v.val)
    rw [he,Fintype.card_coe]
    have hh:=abs_le.mp (hcounts.1 v.val)
    nlinarith only [hh.1,herror,hL]
  have hcodeg (v w:I) (hw:w∉E v):
      (∑u,bipAdj Hloc v u*bipAdj Hloc w u)≤(pH^2+ε)*Fintype.card B:=by
    have hne:v.val≠w.val:=by
      intro he
      have h':v=w:=Subtype.ext he
      apply hw
      simp [E,h']
    have hnF:¬F.Adj v.val w.val:=by
      intro he
      apply hw
      exact Finset.mem_insert_of_mem ((F'.mem_neighborFinset v w).mpr he)
    have he:(∑u:B,bipAdj Hloc v u*bipAdj Hloc w u)=
        (B.filter (fun u=>H v.val u∧H w.val u)).card:=finite_domain_codegree_sum B (H v.val) (H w.val)
    rw [he,Fintype.card_coe]
    have hh:=abs_le.mp (hcounts.2 v.val w.val hne hnF)
    nlinarith only [hh.2,herror]
  have hrowNat (v:I):((∑u:B,relationMultiplicity Hloc v u:ℕ):ℝ)=(B.filter (H v.val)).card:=by
    have hh:=finite_domain_indicator_sum B (H v.val)
    simpa only [relationMultiplicity,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using hh
  have hcolNat (u:B):((∑v:I,relationMultiplicity Hloc v u:ℕ):ℝ)=(I.filter (fun v=>H v u.val)).card:=by
    have hh:=finite_domain_indicator_sum I (fun v=>H v u.val)
    simpa only [relationMultiplicity,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using hh
  apply finite_codegrees_imply_large_cut Hloc pH ε ((Dmax+1:ℕ):ℝ) ζ δ (2*h)
    (by simpa only [Fintype.card_coe] using hI) (by simpa only [Fintype.card_coe] using hB)
    hp hp1 hε (by positivity) hζ hδ hζsmall hh E hE hrow hcodeg
    (by simpa only [Fintype.card_coe] using hbudget)
  · intro v
    rw [hrowNat,Fintype.card_coe]
    have h:=abs_le.mp (hcounts.1 v.val)
    linarith only [h.1,hrowMin]
  · intro u
    rw [hcolNat,Fintype.card_coe]
    have h:=abs_le.mp (hcolumns u.val)
    linarith only [h.1,hcolMin]
end Oberwolfach
