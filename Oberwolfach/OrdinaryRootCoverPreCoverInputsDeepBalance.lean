module

public import Oberwolfach.OrdinaryRootCoverNearGeometryDeepBalance
public import Oberwolfach.OrdinaryRootCoverNonrootComapDegree
public import Oberwolfach.OrdinaryInducedCoverDeletion
public import Oberwolfach.OrdinaryPreCoverPackingInputs

@[expose] public section
/-! Build the pre-cover packing input from the actual root cover, its
post-cover balance profiles, and a reserve on the same nonroot domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_root_cover_precover_inputs_of_deep_balance (P Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r k:ℕ) (hr:3≤r) (ηcover ell b₀ c₀ deep:ℝ) (hell:0≤ell) (hTX:T⊆X) (hWZ:W⊆Z)
    (D:OrdinaryRootCoverNonrootData Q F H X T Z W r ηcover ell)
    (hQP:Q≤P\F)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hdeep:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep)
    (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤b₀)
    (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤c₀)
    (α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c:ℝ)
    (hf:deep+3*ell≤f) (hb:b₀+3*ell+(deep+3*ell)≤binner)
    (hc:c₀+3*ell+(deep+3*ell)≤c):
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:C↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    let Q':=Q\D.rim;let H':=fun v u=>H v u∧¬D.spokes v u;
    let Df:=(ordinaryPhysicalGraph D.rim D.spokes).comap (φ.sumMap ψ);
    ∀σ:Sym2 (A⊕C)→Bool,
    OrdinaryEditedParentFields r hr k α βparent b B h δ εparent (P.induce (A:Set V))
      (Q.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:C)=>H v.val u.val)→
    OrdinaryNonrootGeometryMargins r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c
      (Q'.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:C)=>H' v.val u.val) Xf Zf σ→
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card A→
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card C→
    Nonempty (OrdinaryPreCoverPackingInputs r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c ell
      (P.induce (A:Set V)) (Q.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:C)=>H v.val u.val) Xf Zf Df σ):=by
  intro A C φ ψ Xf Zf Q' H' Df σ fields margins hscaleV hscaleU
  have hsub:(Q.induce (A:Set V))≤(P.induce (A:Set V))\(F.induce (A:Set V)):=by
    intro v w hvw
    exact hQP hvw
  have hg:=ordinary_root_cover_near_geometry_of_deep_balance Q F H X T Z W r k ηcover ell b₀ c₀ deep hell hTX hWZ D hbal hdiv hdeep hinner hcross
    ω βparent β b B εparent εstar η ξ ζ p ε f binner c hf hb hc σ margins
  have hd:=ordinary_induced_cover_deletion_pair Q D.rim H D.spokes T W
  have hcover:=ordinary_root_cover_nonroot_comap_degree Q F H X T Z W r ηcover ell D
  refine ⟨⟨hsub,fields,?_,?_,hscaleV,hscaleU⟩⟩
  · rw [hd.1]
    convert hg using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · exact hcover
end Oberwolfach
