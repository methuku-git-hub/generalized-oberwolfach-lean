module

public import Oberwolfach.OrdinaryTriangleTwoDomainEvent
public import Oberwolfach.OrdinaryRootRepairRowCovers

@[expose] public section
/-! The triangle event only needs column control on the selected hub domain.
Outside columns are repaired on the same sample at the cost of the roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_event_with_selected_columns
    (P F Q:SimpleGraph V) (J:V→U→Prop) (π:Equiv.Perm V) (d D:ℕ)
    (A X Z:Finset V) (B:Finset U) (n:ℕ) (x:Fin n→V)
    (pR pH η θ ρ L:ℝ) (hL:0≤L) (hcap:L+n+D+2*(3*d:ℕ)≤ρ*A.card)
    (hZA:Z⊆A) (hn:(n:ℝ)≤θ*A.card) (hx:Function.Injective x) (hX:∀i,x i∈X)
    (hZ:∀i,x i∉Z) (hroot:∀i,Q.neighborFinset (x i)⊆Z) (hJ:∀i u,J (x i) u→u∈B)
    (hbalance:∀i,|pR*(A∩P.neighborFinset (x i)).card/(2*B.card*pH)-1|≤η)
    (hbal:∀i,Q.degree (x i)=2*(Finset.univ.filter (J (x i))).card)
    (hQ:Q≤P\F) (j:Color) (sample:RawWheelOutcome V U Γ Color)
    (hEvent:OrdinaryTriangleTwoDomainRowEvent P F π d D A X B pR pH η θ ρ j sample):
    let R:=rawWheelGraph P sample\F
    let H:=rawWheelSpokes π d sample j;
    (∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
    (∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L) →
    (∀u∈B,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L) →
    ∃ M:Fin n→Finset (OrdinaryWheel Q F J 3),
      (∀i,OrdinaryRowCover (M i) (x i) Z 0) ∧
      (∀i k,i≠k→Disjoint ((M i).biUnion ordinaryWheelResources) ((M k).biUnion ordinaryWheelResources)):=by
  intro R H hR hrow hcol
  let T:=Finset.univ.image x
  let J':=ordinaryRootColumnRepair H J T B
  have hxT:∀i,x i∈T:=fun i=>Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have ht:(T.card:ℝ)≤n:=by
    have hh:T.card≤n:=by dsimp [T];simpa using (Finset.card_image_le (s:=Finset.univ) (f:=x))
    exact_mod_cast hh
  have hr:=ordinary_root_column_repair_properties H J T B L hL hrow hcol
  have hR':∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L+n:=by
    intro v
    have hh:=hR v
    have hn0:(0:ℝ)≤n:=by positivity
    linarith
  have hrow':∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J' v))).card:ℝ)≤L+n:=by
    intro v
    have hh:=hr.2.2.1 v
    have hn0:(0:ℝ)≤n:=by positivity
    linarith
  have hcol':∀u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J' v u))).card:ℝ)≤L+n:=by
    intro u;have hh:=hr.2.2.2 u;linarith
  have hJ':∀i u,J' (x i) u→u∈B:=by
    intro i u hu;exact hJ i u ((hr.1 (x i) (hxT i) u).mp hu)
  have hbal':∀i,Q.degree (x i)=2*(Finset.univ.filter (J' (x i))).card:=by
    intro i
    have he:Finset.univ.filter (J' (x i))=Finset.univ.filter (J (x i)):=by
      ext u;simp only [Finset.mem_filter,Finset.mem_univ,true_and];exact hr.1 (x i) (hxT i) u
    rw [he]
    exact hbal i
  have hEvt:=hEvent Q J' (L+n) (by positivity) (by linarith) hQ
    (by intro v;convert hR' v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hrow' v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hcol' u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    Z hZA n x hn hx hX hZ hroot hJ' hbalance hbal'
  obtain ⟨M,hM,hcross⟩:=hEvt
  exact ordinary_root_repair_row_covers Q F H J T B n 3 0 x Z hxT hJ M hM hcross
end Oberwolfach
