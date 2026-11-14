module

public import Oberwolfach.OrdinaryRootCoverSharpFullBalance
public import Oberwolfach.OrdinaryNestedCrossBalance
public import Oberwolfach.OrdinaryInducedIntersectionCards

@[expose] public section
/-! Transfer outer-to-inner balance using only the cover's actual cross
error on inner nonroots. The deep root count is never charged directly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_sharp_cross_balance
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell c deep loss:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤c)
    (hdeep:∀v∉X,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep)
    (hdel:∀v∉X,|((D.rim.neighborFinset v∩(X\T)).card:ℝ)-
      2*((Z\W).filter (D.spokes v)).card|≤loss):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    let Q':=Q\D.rim;let H':=fun v u=>H v u∧¬D.spokes v u;
    ∀v:A,v∉Xf→|((((Q'.induce (A:Set V)).neighborFinset v)∩Xf).card:ℝ)-
      2*(Zf.filter (fun u=>H' v.val u.val)).card|≤c+deep+loss:=by
  intro A B Xf Zf Q' H' v hv
  have hvX:v.val∉X:=by simpa [Xf] using hv
  have hX:X∩A=X\T:=by ext z;simp [A]
  have hZ:Z∩B=Z\W:=by ext z;simp [B]
  have hq:=hcross v.val hvX
  have hd:=hdeep v.val hvX
  have hZrow:Z.filter (H v.val)=(Finset.univ.filter (H v.val))∩Z:=by ext u;simp [and_comm]
  have hWrow:W.filter (H v.val)=(Finset.univ.filter (H v.val))∩W:=by ext u;simp [and_comm]
  rw [hZrow] at hq
  rw [hWrow] at hd
  have hn:=ordinary_nested_cross_balance (Q.neighborFinset v.val) (Q.neighborFinset v.val) X T
    (Finset.univ.filter (H v.val)) (Finset.univ.filter (H v.val)) Z W c deep 0 hTX hWZ hq hd
    (by simp [changed]) (by simp [changed])
  have hbase:|((Q.neighborFinset v.val∩(X\T)).card:ℝ)-2*((Z\W).filter (H v.val)).card|≤c+deep:=by
    have he:(Z\W).filter (H v.val)=(Finset.univ.filter (H v.val))∩(Z\W):=by ext u;simp [and_comm]
    rw [he]
    linarith only [hn]
  have hnew:=ordinary_cross_balance_deletion_transfer_at Q D.rim H D.spokes (X\T) (Z\W) v.val (c+deep) loss
    D.rim_sub D.spoke_sub hbase (hdel v.val hvX)
  have hiR:=ordinary_induced_neighbor_intersection_card Q' A X v
  rw [hX] at hiR
  have hiH:=ordinary_induced_spoke_intersection_card H' B Z v.val
  rw [hZ] at hiH
  have he:(Zf.filter (fun u=>H' v.val u.val))=Finset.univ.filter (fun u:B=>H' v.val u.val ∧ u.val∈Z):=by ext u;simp [Zf,and_comm]
  have hiH':(Finset.univ.filter (fun u:B=>H' v.val u.val∧u.val∈Z)).card=
      ((Finset.univ.filter (H' v.val))∩(Z\W)).card:=by
    convert hiH using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hiR':(((Q'.induce (A:Set V)).neighborFinset v)∩Xf).card=(Q'.neighborFinset v.val∩(X\T)).card:=by
    convert hiR using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hn':|((Q'.neighborFinset v.val∩(X\T)).card:ℝ)-
      2*((Finset.univ.filter (H' v.val))∩(Z\W)).card|≤c+deep+loss:=by
    convert hnew using 1 <;> congr! 8 <;> first | (ext u;simp [H',and_comm]) | exact Subsingleton.elim _ _
  rw [he,hiH']
  convert hn' using 1
  apply congrArg abs
  apply congrArg (fun x:ℝ=>x-2*((Finset.univ.filter (H' v.val))∩(Z\W)).card)
  have hiRreal:(((Q'.induce (A:Set V)).neighborFinset v∩Xf).card:ℝ)=
      ((Q'.neighborFinset v.val∩(X\T)).card:ℝ):=by exact_mod_cast hiR'
  convert hiRreal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
