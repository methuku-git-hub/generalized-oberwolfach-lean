module

public import Oberwolfach.FiniteCodegreeUniformCut
public import Oberwolfach.BipartiteLargeCutEmbedding
public import Oberwolfach.TypedMatrixRealization

@[expose] public section
/-! Uniform degree and codegree estimates imply the normalized large-cut
    condition used by the sparse correction theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y:Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem finite_codegrees_imply_large_cut
    (H:X→Y→Prop) (p ε D ζ δ h:ℝ)
    (hn:0<Fintype.card X) (hm:0<Fintype.card Y)
    (hp:0<p) (hp1:p≤1) (hε:0≤ε) (hD:0≤D) (hζ:0≤ζ)
    (hδ:δ≤p/16) (hζsmall:ζ≤p^2/128) (hh:h≤p/8)
    (E:X→Finset X) (hE:∀x,((E x).card:ℝ)≤D)
    (hrow:∀x,(p-ε)*Fintype.card Y≤∑u,bipAdj H x u)
    (hcodeg:∀x y,y∉E x→∑u,bipAdj H x u*bipAdj H y u≤(p^2+ε)*Fintype.card Y)
    (hbudget:3*ε*(Fintype.card X:ℝ)^2*(Fintype.card Y:ℝ)^2+
      D*Fintype.card X*(Fintype.card Y:ℝ)^2≤(ζ*Fintype.card X*Fintype.card Y)^2)
    (hrowMin:∀x,p*(Fintype.card Y:ℝ)/2≤((∑u,relationMultiplicity H x u:ℕ):ℝ))
    (hcolMin:∀u,p*(Fintype.card X:ℝ)/2≤((∑x,relationMultiplicity H x u:ℕ):ℝ)):
    BipartiteLargeCut (relationMultiplicity H) δ h:=by
  have hquad:=finite_codegree_uniform_cut H p ε D ζ hp.le hp1 hε hD hζ E hE hrow hcodeg hbudget
  intro S T hST
  have hn':(0:ℝ)<Fintype.card X:=by exact_mod_cast hn
  have hm':(0:ℝ)<Fintype.card Y:=by exact_mod_cast hm
  have hl:(1-2*δ)*(Fintype.card X:ℝ)*Fintype.card Y<
      (Fintype.card Y:ℝ)*S.card+(Fintype.card X:ℝ)*T.card:=by
    have hh':=(mul_lt_mul_of_pos_right hST (mul_pos hn' hm'))
    have he:((S.card:ℝ)/Fintype.card X+(T.card:ℝ)/Fintype.card Y)*
        ((Fintype.card X:ℝ)*Fintype.card Y)=
        (Fintype.card Y:ℝ)*S.card+(Fintype.card X:ℝ)*T.card:=by field_simp <;> ring
    rw [he] at hh'
    nlinarith only [hh']
  have hcut:=bipartiteMatrixCut_large_of_degree_and_quadratic (relationMultiplicity H)
    (by intro x u;unfold relationMultiplicity;split_ifs <;> omega) hn hm p p δ ζ hp hp1 le_rfl hδ hζsmall hrowMin hcolMin
    (by intro S T;convert hquad S T using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) S T hl
  rw [bipartiteLargeCut_sum_restrict,bipartite_normalized_cut_scale hn hm]
  have hmin:0≤min ((Fintype.card Y:ℝ)*S.card) ((Fintype.card X:ℝ)*T.card):=by positivity
  exact (mul_le_mul_of_nonneg_right hh hmin).trans hcut
end Oberwolfach
