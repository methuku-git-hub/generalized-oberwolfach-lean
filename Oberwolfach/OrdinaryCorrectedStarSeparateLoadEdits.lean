module

public import Oberwolfach.OrdinaryCorrectedStarSeparateLoadOuter
public import Oberwolfach.OrdinaryReservedInnerStarEditBounds
public import Oberwolfach.OrdinaryDeepCoverSeparateLoadEvent

@[expose] public section
/-! The finite same-sample triangle cover event covers the correction star
    and then all protected roots, with the corrected inner star reserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_corrected_star_separate_load_from_original_edits
    (P F Q D:SimpleGraph V) (H J:V→U→Prop) (I T:Finset V) (B W:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (m K:ℕ) (a aLoad ρ θ L Lbase:ℝ) (D₀:ℕ) (event:OrdinaryDeepCoverSeparateLoadEvent m K a aLoad ρ θ P F B π d j raw)
    (hTI:T⊆I) (hWB:W⊆B) (hDI:D≤spanningRestriction Q I)
    (hJ:∀v u,J v u→H v u∧v∈I∧u∈B)
    (hdegree:∀x:V⊕U,(ordinaryPhysicalGraph D J).degree x≤D₀)
    (hDscale:(D₀:ℝ)≤aLoad*Fintype.card V)
    (hEscale:((Fintype.card (V⊕U)*D₀:ℕ):ℝ)≤aLoad^2*(Fintype.card V:ℝ)^2)
    (hI:(I.card:ℝ)≤a*Fintype.card V) (hT:(T.card:ℝ)≤θ*Fintype.card V)
    (hW:(2*W.card:ℝ)≤L) (hL:0≤L) (hLsmall:L≤ρ*Fintype.card V)
    (hF:∀v,(F.degree v:ℝ)≤L)
    (hQP:Q≤P\F) (hbudgetI:Lbase+I.card≤L) (hbudgetB:Lbase+B.card≤L)
    (hQRbase:∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤Lbase)
    (hHrbase:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v)) (Finset.univ.filter (H v))).card:ℝ)≤Lbase)
    (hHcbase:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤Lbase)
    (hQbal:∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hHdiv:∀u∈W,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (hCbal:∀v∈T,((spanningRestriction Q I)\D).degree v=
      2*(Finset.univ.filter (fun u=>(H v u∧v∈I∧u∈B)∧¬J v u)).card)
    (hKdiv:∀u∈W,(m+1)∣(Finset.univ.filter (fun v=>(H v u∧v∈I∧u∈B)∧¬J v u)).card):
    let R:=ordinaryRimRootStar ((spanningRestriction Q I)\D) T;
    let S:=ordinarySpokeRootStar (fun v u=>(H v u∧v∈I∧u∈B)∧¬J v u) T W;
    let Qout:=Q\R;
    let Hout:=fun v u=>H v u∧¬S v u;
    let E:=(ordinaryHostResources D J).filter (ordinaryResourceTouchesRoots T W);
    ∃M:Finset (OrdinaryWheel Qout F Hout (m+1)),
      (∀A∈M,∀B'∈M,A≠B'→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B')) ∧
      M.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Qout I)
        (fun v u=>Hout v u∧v∈I∧u∈B)=E ∧
      (∀v∈T,∀w,(ordinaryWheelRimGraph M).Adj v w↔Qout.Adj v w) ∧
      (∀v∈T,∀u,ordinaryPackingSpokes M v u↔Hout v u) ∧
      (∀u∈W,∀v,ordinaryPackingSpokes M v u↔Hout v u) ∧
      (∀v∉I,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inl v):ℝ)≤
        18*aLoad*Fintype.card V+3*((W.card:ℝ)+(K+1)*T.card)) ∧
      (∀u∉B,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inr u):ℝ)≤
        3*aLoad*Fintype.card V*(m+1)+(T.card:ℝ)*(m+1)) :=by
  intro R S Qout Hout E
  have hC:((spanningRestriction Q I)\D)≤spanningRestriction Q I:=sdiff_le
  have hK:∀v u,((H v u∧v∈I∧u∈B)∧¬J v u)→H v u∧v∈I∧u∈B:=by intro v u h;exact h.1
  have he:=ordinary_reserved_inner_star_edit_bounds (rawWheelGraph P raw) Q ((spanningRestriction Q I)\D)
    (rawWheelSpokes π d raw j) H (fun v u=>(H v u∧v∈I∧u∈B)∧¬J v u) I T B W Lbase hC hK
    hQRbase hHrbase hHcbase
  change (∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Qout.neighborFinset v)).card:ℝ)≤Lbase+I.card) ∧
    (∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v)) (Finset.univ.filter (Hout v))).card:ℝ)≤Lbase+B.card) ∧
    (∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u))
      (Finset.univ.filter (fun v=>Hout v u))).card:ℝ)≤Lbase+I.card) at he
  apply ordinary_corrected_star_deep_cover_separate_load_outer P F Q D H J I T B W π d j raw m K a aLoad ρ θ L D₀ event
    hTI hWB hDI hJ hdegree hDscale hEscale hI hT hW hL hLsmall hF hQbal hHdiv
    (by intro v hv;convert hCbal v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u hu;convert hKdiv u hu using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  · exact sdiff_le.trans hQP
  · intro v;convert (he.1 v).trans hbudgetI using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v;convert (he.2.1 v).trans hbudgetB using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro u;convert (he.2.2 u).trans hbudgetI using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
