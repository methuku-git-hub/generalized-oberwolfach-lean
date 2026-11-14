module

public import Oberwolfach.OrdinaryFineWheelCoverData
public import Oberwolfach.OrdinaryRootCoverSharpReferenceData

@[expose] public section
/-! Retain the selected cover's small crossing error in the pre-reserve
reference, with balance margins independent of the root-cardinality load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]

theorem ordinary_fine_cover_sharp_reference_general_load
    (m k loadK:ℕ) (hm:2≤m) (ξroot κ:ℝ) (P Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (hTX:T⊆X) (hWZ:W⊆Z)
    (hξ:0≤ξroot) (hκ:0≤κ) (b₀ c₀ deep:ℝ) (hb:0≤b₀) (hdeep0:0≤deep)
    (hcover:OrdinaryFineWheelCoverResult m loadK ξroot κ Q F H X T Z W)
    (hQP:Q≤P\F) (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (hdeep:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep)
    (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤b₀)
    (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤c₀)
    (α ω βparent β b B h δ εparent εstar η ξ ζ p ε:ℝ):
    let ell:=max (18*κ*Fintype.card V+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*κ*Fintype.card V*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1));
    let cover:=10*ξroot*X.card;let loss:=12*κ*Fintype.card V;
    let f:=deep+2*cover;let binner:=b₀+deep+4*cover;let c:=c₀+deep+loss;
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    OrdinaryEditedParentFields (m+1) (by omega) k α βparent b B h δ εparent (P.induce (A:Set V))
      (Q.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:C)=>H v.val u.val)→
    OrdinaryNonrootGeometryStatic (m+1) k ω βparent β b B εparent εstar η ξ ζ p ε f binner c Xf Zf→
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card A→
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card C→
    ∃D:OrdinaryRootCoverNonrootData Q F H X T Z W (m+1) cover ell,
      Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W (m+1) k (by omega) cover ell b₀ c₀ deep loss D
        α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c):=by
  intro ell cover loss f binner c A C Xf Zf hfields hstatic hscaleV hscaleU
  have hell:0≤ell:=by dsimp [ell];positivity
  have hcover0:0≤cover:=by dsimp [cover];positivity
  have hdata:∃D:OrdinaryRootCoverNonrootData Q F H X T Z W (m+1) cover ell,
      ∀v,|((D.rim.neighborFinset v∩(X\T)).card:ℝ)-2*((Z\W).filter (D.spokes v)).card|≤loss:=by
    exact ordinary_fine_wheel_cover_data m loadK ξroot κ Q F H X T Z W hTX hWZ hcover
  obtain ⟨D,hdel⟩:=hdata
  refine ⟨D,⟨⟨hell,hcover0,hb,hdeep0,hQP,hbal,hdiv,hTX,hWZ,hdeep,hinner,hcross,?_,le_rfl,le_rfl,le_rfl,?_,?_,?_,?_⟩⟩⟩
  · intro v hv
    convert hdel v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hfields using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hstatic using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hscaleV using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hscaleU using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
