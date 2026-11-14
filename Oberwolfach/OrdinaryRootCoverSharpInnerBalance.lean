module

public import Oberwolfach.OrdinaryRootCoverSharpFullBalance
public import Oberwolfach.OrdinaryNestedCrossBalance
public import Oberwolfach.OrdinaryInducedIntersectionCards

@[expose] public section
/-! On the inner pair, the root-cover deletion is charged only to its
induced degree. This yields an inner balance bound independent of the
cover's larger full nonroot degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_sharp_inner_balance
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell b deep:ℝ)
    (hη:0≤η) (hb:0≤b) (hdeep0:0≤deep) (hTX:T⊆X) (hWZ:W⊆Z)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤b)
    (hdeep:∀v∈X,v∉T→|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    let Q':=Q\D.rim;let H':=fun v u=>H v u∧¬D.spokes v u;
    ∀v:A,|((spanningRestriction (Q'.induce (A:Set V)) Xf).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>H' v.val u.val∧v∈Xf∧u∈Zf)).card|≤b+deep+4*η:=by
  intro A B Xf Zf Q' H' v
  have hcross:=ordinary_root_cover_sharp_deep_cross Q F H X T Z W r η ell deep hη hdeep0 hTX hWZ D hdeep
  have hX:X∩A=X\T:=by ext z;simp [A]
  have hZ:Z∩B=Z\W:=by ext z;simp [B]
  have hvT:v.val∉T:=(Finset.mem_sdiff.mp v.property).2
  by_cases hv:v.val∈X
  · have hvf:v∈Xf:=by simp [Xf,hv]
    have hbase:=hinner v.val
    have he0:(Finset.univ.filter (fun u=>H v.val u∧v.val∈X∧u∈Z))=Z.filter (H v.val):=by
      ext u;simp [hv,and_comm]
    rw [spanningRestriction_degree,if_pos hv,he0] at hbase
    have hdel:=ordinary_physical_cost_cross_bound D.rim D.spokes X X Z Z (Finset.Subset.refl _) (Finset.Subset.refl _)
      v.val hv η D.inner_degree
    have hinside:=ordinary_cross_balance_deletion_transfer_at Q D.rim H D.spokes X Z v.val b (2*η)
      D.rim_sub D.spoke_sub hbase hdel
    have hs:Z.filter (H' v.val)=(Finset.univ.filter (H' v.val))∩Z:=by ext u;simp [and_comm]
    have ht:W.filter (H' v.val)=(Finset.univ.filter (H' v.val))∩W:=by ext u;simp [and_comm]
    rw [hs] at hinside
    have hd:=hcross v.val hvT
    rw [ht] at hd
    have hh:=ordinary_nested_cross_balance (Q'.neighborFinset v.val) (Q'.neighborFinset v.val) X T
      (Finset.univ.filter (H' v.val)) (Finset.univ.filter (H' v.val)) Z W (b+2*η) (deep+2*η) 0 hTX hWZ
      hinside hd (by simp [changed]) (by simp [changed])
    have hiR:=ordinary_induced_neighbor_intersection_card Q' A X v
    rw [hX] at hiR
    have hiH:=ordinary_induced_spoke_intersection_card H' B Z v.val
    rw [hZ] at hiH
    have he:(Finset.univ.filter (fun u:B=>H' v.val u.val∧v∈Xf∧u∈Zf))=
        Finset.univ.filter (fun u:B=>H' v.val u.val∧u.val∈Z):=by ext u;simp [Zf,hvf]
    have hiH':(Finset.univ.filter (fun u:B=>H' v.val u.val∧u.val∈Z)).card=
        ((Finset.univ.filter (H' v.val))∩(Z\W)).card:=by
      convert hiH using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hiR':(((Q'.induce (A:Set V)).neighborFinset v)∩Xf).card=(Q'.neighborFinset v.val∩(X\T)).card:=by
      convert hiR using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    rw [spanningRestriction_degree,if_pos hvf,he,hiH']
    have ht:|((Q'.neighborFinset v.val∩(X\T)).card:ℝ)-
        2*((Finset.univ.filter (H' v.val))∩(Z\W)).card|≤b+deep+4*η:=by linarith only [hh]
    convert ht using 1
    apply congrArg abs
    apply congrArg (fun x:ℝ=>x-2*((Finset.univ.filter (H' v.val))∩(Z\W)).card)
    have hiRreal:(((Q'.induce (A:Set V)).neighborFinset v∩Xf).card:ℝ)=
        ((Q'.neighborFinset v.val∩(X\T)).card:ℝ):=by exact_mod_cast hiR'
    convert hiRreal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · have hvf:v∉Xf:=by simpa [Xf] using hv
    rw [spanningRestriction_degree,if_neg hvf]
    have he:(Finset.univ.filter (fun u:B=>H' v.val u.val∧v∈Xf∧u∈Zf))=∅:=by ext u;simp [hvf]
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero,abs_zero]
    linarith
end Oberwolfach
