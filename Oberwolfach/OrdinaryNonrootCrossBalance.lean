module

public import Oberwolfach.OrdinaryNonrootIntersectionChange
public import Oberwolfach.OrdinaryInducedIntersectionCards

@[expose] public section
/-! Cross-balance survives deletion of adaptive roots and bounded edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_cross_balance
    (Q Q₀:SimpleGraph V) (H H₀:V→U→Prop) (X T:Finset V) (Z W:Finset U) (L c:ℝ)
    (hR:∀v∉T,((changed (Q.neighborFinset v) (Q₀.neighborFinset v)).card:ℝ)≤L)
    (hH:∀v∉T,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (H₀ v))).card:ℝ)≤L)
    (hcross:∀v∉X,|((Q₀.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H₀ v)).card|≤c):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    ∀v:A,v∉Xf→|((((Q.induce (A:Set V)).neighborFinset v)∩Xf).card:ℝ)-
      2*(Zf.filter (fun u=>H v.val u.val)).card|≤c+3*L+T.card+2*W.card:=by
  intro A B Xf Zf v hv
  have hvT:v.val∉T:=(Finset.mem_sdiff.mp v.property).2
  have hvX:v.val∉X:=by simpa [Xf] using hv
  have hX:X∩A=X\T:=by ext z;simp [A]
  have hZ:Z∩B=Z\W:=by ext z;simp [B]
  have hr:=ordinary_nonroot_intersection_change (Q.neighborFinset v.val) (Q₀.neighborFinset v.val) X T L (hR v.val hvT)
  have hh:=ordinary_nonroot_intersection_change (Finset.univ.filter (H v.val)) (Finset.univ.filter (H₀ v.val)) Z W L (hH v.val hvT)
  have hiR:=ordinary_induced_neighbor_intersection_card Q A X v
  rw [hX] at hiR
  have hiH:=ordinary_induced_spoke_intersection_card H B Z v.val
  rw [hZ] at hiH
  have he:(Zf.filter (fun u=>H v.val u.val))=Finset.univ.filter (fun u:B=>H v.val u.val ∧ u.val∈Z):=by
    ext u;simp [Zf,and_comm]
  have ho:=hcross v.val hvX
  have he₀:(Z.filter (H₀ v.val))=(Finset.univ.filter (H₀ v.val))∩Z:=by ext u;simp [and_comm]
  rw [he₀] at ho
  rw [he,hiH,hiR]
  have hr':=abs_le.mp hr
  have hh':=abs_le.mp hh
  have ho':=abs_le.mp ho
  apply abs_le.mpr
  constructor <;> linarith only [hr'.1,hr'.2,hh'.1,hh'.2,ho'.1,ho'.2]
end Oberwolfach
