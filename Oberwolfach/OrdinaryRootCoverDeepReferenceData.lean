module

public import Oberwolfach.OrdinaryRootCoverPreCoverInputsDeepBalance
public import Oberwolfach.OrdinaryNonrootGeometryStatic

@[expose] public section
/-! The pre-reserve data for an actual selected deep-root cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

structure OrdinaryRootCoverDeepReferenceData (P Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r k:ℕ) (hr:3≤r) (ηcover ell b₀ c₀ deep:ℝ)
    (D:OrdinaryRootCoverNonrootData Q F H X T Z W r ηcover ell)
    (α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c:ℝ) where
  ell_nonneg:0≤ell
  graph_sub:Q≤P\F
  balance:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card
  divisible:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card
  deep_subset_V:T⊆X
  deep_subset_U:W⊆Z
  deep_balance:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep
  inner_balance:∀v,|((spanningRestriction Q X).degree v:ℝ)-
    2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤b₀
  cross_balance:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤c₀
  full_margin:deep+3*ell≤f
  inner_margin:b₀+3*ell+(deep+3*ell)≤binner
  cross_margin:c₀+3*ell+(deep+3*ell)≤c
  fields:
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    OrdinaryEditedParentFields r hr k α βparent b B h δ εparent (P.induce (A:Set V))
      (Q.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:C)=>H v.val u.val)
  static:
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    OrdinaryNonrootGeometryStatic r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c Xf Zf
  scale_V:
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card A
  scale_U:
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card C
end Oberwolfach
