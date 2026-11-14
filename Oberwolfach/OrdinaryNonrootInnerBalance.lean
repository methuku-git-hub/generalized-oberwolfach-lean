module

public import Oberwolfach.OrdinaryNonrootIntersectionChange
public import Oberwolfach.OrdinaryInducedIntersectionCards
public import Oberwolfach.GraphSelectionDegrees

@[expose] public section
/-! Inner balance survives deletion of adaptive roots and bounded edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_inner_balance
    (Q Q₀:SimpleGraph V) (H H₀:V→U→Prop) (X T:Finset V) (Z W:Finset U) (L b:ℝ) (hL:0≤L)
    (hR:∀v∉T,((changed (Q.neighborFinset v) (Q₀.neighborFinset v)).card:ℝ)≤L)
    (hH:∀v∉T,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (H₀ v))).card:ℝ)≤L)
    (hinner:∀v,|((spanningRestriction Q₀ X).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H₀ v u∧v∈X∧u∈Z)).card|≤b):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    ∀v:A,|((spanningRestriction (Q.induce (A:Set V)) Xf).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>H v.val u.val∧v∈Xf∧u∈Zf)).card|≤
        b+3*L+T.card+2*W.card:=by
  intro A B Xf Zf v
  have hvT:v.val∉T:=(Finset.mem_sdiff.mp v.property).2
  have hX:X∩A=X\T:=by ext z;simp [A]
  have hZ:Z∩B=Z\W:=by ext z;simp [B]
  by_cases hv:v.val∈X
  · have hvf:v∈Xf:=by simp [Xf,hv]
    have hr:=ordinary_nonroot_intersection_change (Q.neighborFinset v.val) (Q₀.neighborFinset v.val) X T L (hR v.val hvT)
    have hh:=ordinary_nonroot_intersection_change (Finset.univ.filter (H v.val)) (Finset.univ.filter (H₀ v.val)) Z W L (hH v.val hvT)
    have hiR:=ordinary_induced_neighbor_intersection_card Q A X v
    rw [hX] at hiR
    have hiH:=ordinary_induced_spoke_intersection_card H B Z v.val
    rw [hZ] at hiH
    have he:(Finset.univ.filter (fun u:B=>H v.val u.val∧v∈Xf∧u∈Zf))=
        Finset.univ.filter (fun u:B=>H v.val u.val∧u.val∈Z):=by ext u;simp [Zf,hvf]
    have he₀:(Finset.univ.filter (fun u=>H₀ v.val u∧v.val∈X∧u∈Z))=
        (Finset.univ.filter (H₀ v.val))∩Z:=by ext u;simp [hv]
    have ho:=hinner v.val
    rw [spanningRestriction_degree,if_pos hv,he₀] at ho
    rw [spanningRestriction_degree,if_pos hvf,he,hiH,hiR]
    have hr':=abs_le.mp hr
    have hh':=abs_le.mp hh
    have ho':=abs_le.mp ho
    apply abs_le.mpr
    constructor <;> linarith only [hr'.1,hr'.2,hh'.1,hh'.2,ho'.1,ho'.2]
  · have hvf:v∉Xf:=by simpa [Xf] using hv
    have hb:0≤b:=(abs_nonneg _).trans (hinner v.val)
    rw [spanningRestriction_degree,if_neg hvf]
    have he:(Finset.univ.filter (fun u:B=>H v.val u.val∧v∈Xf∧u∈Zf))=∅:=by ext u;simp [hvf]
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero,abs_zero]
    positivity
end Oberwolfach
