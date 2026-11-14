module

public import Oberwolfach.DegreeCodegreeVariance

@[expose] public section

/-! The large-cut lower bound used in the ordinary endpoint assignment,
with the exceptional-pair contribution retained explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem codegree_cut_numeric (p ε D b s t v η:ℝ)
    (hp:0<p) (hb:0<b) (hη:0<η) (hs:η*b≤s) (ht:η*b≤t)
    (hε:ε≤p^2*η/24) (hD:D≤p^2*η^2*b/8)
    (hq:(v-p*s*t)^2≤t*(3*ε*s^2*b+D*s*b)) : p/2*s*t≤v := by
  have hspos:0<s:=(mul_pos hη hb).trans_le hs
  have htpos:0<t:=(mul_pos hη hb).trans_le ht
  have hεb:3*ε*b≤p^2*t/8:=by
    have hh:=mul_le_mul_of_nonneg_right hε hb.le
    have hh':=mul_le_mul_of_nonneg_left ht (sq_nonneg p)
    nlinarith only [hh,hh']
  have hproduct:η^2*b^2≤s*t:=by
    have hh:=mul_le_mul hs ht (mul_pos hη hb).le hspos.le
    nlinarith only [hh]
  have hDb:D*b≤p^2*s*t/8:=by
    have hh:=mul_le_mul_of_nonneg_right hD hb.le
    have hh':=mul_le_mul_of_nonneg_left hproduct (sq_nonneg p)
    nlinarith only [hh,hh']
  have hterms:3*ε*s^2*b+D*s*b≤p^2*s^2*t/4:=by
    have hh:=mul_le_mul_of_nonneg_right hεb (sq_nonneg s)
    have hh':=mul_le_mul_of_nonneg_right hDb hspos.le
    nlinarith only [hh,hh']
  have hu:=mul_le_mul_of_nonneg_left hterms htpos.le
  have hu':(v-p*s*t)^2≤(p*s*t/2)^2:=by nlinarith only [hq,hu]
  by_contra hv
  have hv':v<p*s*t/2:=by linarith only [lt_of_not_ge hv]
  have hpos:0<p*s*t/2:=by positivity
  have hsq:(p*s*t/2)^2<(p*s*t-v)^2:=
    (sq_lt_sq₀ hpos.le (by linarith only [hv',hpos])).mpr (by linarith only [hv'])
  nlinarith only [hsq,hu']

theorem bipartite_cuts_from_degrees_and_codegrees {X Y:Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (H:X→Y→Prop) (p ε D η:ℝ)
    (hp:0<p) (hp1:p≤1) (hε:0≤ε) (hη:0<η) (hb:0<Fintype.card Y)
    (E:X→Finset X) (hE:∀ x,((E x).card:ℝ)≤D)
    (hrow:∀ x,(p-ε)*Fintype.card Y≤∑ u,bipAdj H x u)
    (hcodeg:∀ x y,y∉E x → ∑ u,bipAdj H x u*bipAdj H y u≤(p^2+ε)*Fintype.card Y)
    (hsmall:ε≤p^2*η/24) (hlarge:D≤p^2*η^2*Fintype.card Y/8)
    (S:Finset X) (T:Finset Y)
    (hS:η*Fintype.card Y≤(S.card:ℝ)) (hT:η*Fintype.card Y≤(T.card:ℝ)) :
    p/2*S.card*T.card≤(bipartiteMatrixCut (fun x u=>if H x u then 1 else 0) S T:ℝ) := by
  exact codegree_cut_numeric p ε D (Fintype.card Y) S.card T.card
    (bipartiteMatrixCut (fun x u=>if H x u then 1 else 0) S T) η
    hp (Nat.cast_pos.mpr hb) hη hS hT hsmall hlarge
    (degree_codegree_cut_square H p ε D hp.le hp1 hε E hE hrow hcodeg S T)

end Oberwolfach
