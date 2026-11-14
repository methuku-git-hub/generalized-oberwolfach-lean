module

public import Oberwolfach.DegreeCodegreeCuts

@[expose] public section
/-! Degree and codegree estimates with a bounded exceptional set imply
    a uniform quadratic-error estimate for all bipartite cuts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y:Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem finite_codegree_uniform_cut
    (H:X→Y→Prop) (p ε D ζ:ℝ) (hp:0≤p) (hp1:p≤1) (hε:0≤ε) (hD:0≤D) (hζ:0≤ζ)
    (E:X→Finset X) (hE:∀x,((E x).card:ℝ)≤D)
    (hrow:∀x,(p-ε)*Fintype.card Y≤∑u,bipAdj H x u)
    (hcodeg:∀x y,y∉E x→∑u,bipAdj H x u*bipAdj H y u≤(p^2+ε)*Fintype.card Y)
    (hbudget:3*ε*(Fintype.card X:ℝ)^2*(Fintype.card Y:ℝ)^2+
      D*Fintype.card X*(Fintype.card Y:ℝ)^2≤(ζ*Fintype.card X*Fintype.card Y)^2):
    ∀S:Finset X,∀T:Finset Y,
      |(bipartiteMatrixCut (fun x u=>if H x u then 1 else 0) S T:ℝ)-p*S.card*T.card|≤
        ζ*Fintype.card X*Fintype.card Y:=by
  intro S T
  let n:ℝ:=Fintype.card X
  let m:ℝ:=Fintype.card Y
  let a:ℝ:=S.card
  let b:ℝ:=T.card
  have hn:0≤n:=by dsimp [n];positivity
  have hm:0≤m:=by dsimp [m];positivity
  have ha:0≤a:=by dsimp [a];positivity
  have hb:0≤b:=by dsimp [b];positivity
  have han:a≤n:=by dsimp [a,n];exact_mod_cast Finset.card_le_univ S
  have hbm:b≤m:=by dsimp [b,m];exact_mod_cast Finset.card_le_univ T
  have ha2:a^2≤n^2:=by nlinarith
  have h1:=mul_le_mul_of_nonneg_left ha2 (show 0≤3*ε*m by positivity)
  have h2:=mul_le_mul_of_nonneg_left han (show 0≤D*m by positivity)
  have hterms:3*ε*a^2*m+D*a*m≤3*ε*n^2*m+D*n*m:=by nlinarith only [h1,h2]
  have hterm0:0≤3*ε*n^2*m+D*n*m:=by positivity
  have hleft:=mul_le_mul_of_nonneg_left hterms hb
  have hright:=mul_le_mul_of_nonneg_right hbm hterm0
  have hupper:b*(3*ε*a^2*m+D*a*m)≤(ζ*n*m)^2:=by
    change 3*ε*n^2*m^2+D*n*m^2≤(ζ*n*m)^2 at hbudget
    nlinarith only [hleft,hright,hbudget]
  have hq:=degree_codegree_cut_square H p ε D hp hp1 hε E hE hrow hcodeg S T
  have hs:(0:ℝ)≤ζ*n*m:=by positivity
  apply (sq_le_sq₀ (abs_nonneg _) hs).mp
  rw [sq_abs]
  dsimp [n,m,a,b] at hupper
  exact hq.trans hupper
end Oberwolfach
