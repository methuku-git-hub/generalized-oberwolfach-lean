module

public import Oberwolfach.OrdinaryNestedCrossBalance
public import Oberwolfach.OrdinaryInducedIntersectionCards
public import Oberwolfach.GraphSelectionDegrees

@[expose] public section
/-! On the nonroot domain, inner and cross balance can use a bound on the
actual deep cross discrepancy in place of the size of the deep pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_balanced_deep_profiles
    (Q Q₀:SimpleGraph V) (H H₀:V→U→Prop) (X T:Finset V) (Z W:Finset U) (L b c deep:ℝ)
    (hL:0≤L) (hTX:T⊆X) (hWZ:W⊆Z)
    (hR:∀v∉T,((changed (Q.neighborFinset v) (Q₀.neighborFinset v)).card:ℝ)≤L)
    (hH:∀v∉T,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (H₀ v))).card:ℝ)≤L)
    (hdeep:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep)
    (hinner:∀v,|((spanningRestriction Q₀ X).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H₀ v u∧v∈X∧u∈Z)).card|≤b)
    (hcross:∀v∉X,|((Q₀.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H₀ v)).card|≤c):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    (∀v:A,|((spanningRestriction (Q.induce (A:Set V)) Xf).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>H v.val u.val∧v∈Xf∧u∈Zf)).card|≤b+3*L+deep) ∧
    (∀v:A,v∉Xf→|((((Q.induce (A:Set V)).neighborFinset v)∩Xf).card:ℝ)-
      2*(Zf.filter (fun u=>H v.val u.val)).card|≤c+3*L+deep):=by
  intro A B Xf Zf
  have hX:X∩A=X\T:=by ext z;simp [A]
  have hZ:Z∩B=Z\W:=by ext z;simp [B]
  constructor
  · intro v
    have hvT:v.val∉T:=(Finset.mem_sdiff.mp v.property).2
    by_cases hv:v.val∈X
    · have hvf:v∈Xf:=by simp [Xf,hv]
      have he₀:(Finset.univ.filter (fun u=>H₀ v.val u∧v.val∈X∧u∈Z))=
          (Finset.univ.filter (H₀ v.val))∩Z:=by ext u;simp [hv]
      have ho:=hinner v.val
      rw [spanningRestriction_degree,if_pos hv,he₀] at ho
      have hd:=hdeep v.val hvT
      have hdEq:W.filter (H v.val)=(Finset.univ.filter (H v.val))∩W:=by ext u;simp [and_comm]
      rw [hdEq] at hd
      have hh:=ordinary_nested_cross_balance (Q.neighborFinset v.val) (Q₀.neighborFinset v.val) X T
        (Finset.univ.filter (H v.val)) (Finset.univ.filter (H₀ v.val)) Z W b deep L hTX hWZ ho hd (hR v.val hvT) (hH v.val hvT)
      have hiR:=ordinary_induced_neighbor_intersection_card Q A X v
      rw [hX] at hiR
      have hiH:=ordinary_induced_spoke_intersection_card H B Z v.val
      rw [hZ] at hiH
      have he:(Finset.univ.filter (fun u:B=>H v.val u.val∧v∈Xf∧u∈Zf))=
          Finset.univ.filter (fun u:B=>H v.val u.val∧u.val∈Z):=by ext u;simp [Zf,hvf]
      rw [spanningRestriction_degree,if_pos hvf,he,hiH,hiR]
      exact hh
    · have hvf:v∉Xf:=by simpa [Xf] using hv
      have hb:0≤b:=(abs_nonneg _).trans (hinner v.val)
      have hd:0≤deep:=(abs_nonneg _).trans (hdeep v.val hvT)
      rw [spanningRestriction_degree,if_neg hvf]
      have he:(Finset.univ.filter (fun u:B=>H v.val u.val∧v∈Xf∧u∈Zf))=∅:=by ext u;simp [hvf]
      rw [he]
      simp only [Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero,abs_zero]
      linarith
  · intro v hv
    have hvT:v.val∉T:=(Finset.mem_sdiff.mp v.property).2
    have hvX:v.val∉X:=by simpa [Xf] using hv
    have he₀:Z.filter (H₀ v.val)=(Finset.univ.filter (H₀ v.val))∩Z:=by ext u;simp [and_comm]
    have hdEq:W.filter (H v.val)=(Finset.univ.filter (H v.val))∩W:=by ext u;simp [and_comm]
    have ho:=hcross v.val hvX
    rw [he₀] at ho
    have hd:=hdeep v.val hvT
    rw [hdEq] at hd
    have hh:=ordinary_nested_cross_balance (Q.neighborFinset v.val) (Q₀.neighborFinset v.val) X T
      (Finset.univ.filter (H v.val)) (Finset.univ.filter (H₀ v.val)) Z W c deep L hTX hWZ ho hd (hR v.val hvT) (hH v.val hvT)
    have hiR:=ordinary_induced_neighbor_intersection_card Q A X v
    rw [hX] at hiR
    have hiH:=ordinary_induced_spoke_intersection_card H B Z v.val
    rw [hZ] at hiH
    have he:(Zf.filter (fun u=>H v.val u.val))=Finset.univ.filter (fun u:B=>H v.val u.val ∧ u.val∈Z):=by ext u;simp [Zf,and_comm]
    rw [he,hiH,hiR]
    exact hh
end Oberwolfach
