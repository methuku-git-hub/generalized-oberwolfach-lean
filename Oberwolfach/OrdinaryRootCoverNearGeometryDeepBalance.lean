module

public import Oberwolfach.OrdinaryNonrootGeometryMargins
public import Oberwolfach.OrdinaryRootCoverDeepBalanceProfiles

@[expose] public section
/-! Combine the actual post-cover balance profiles with the remaining
nonroot geometry and sample margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_root_cover_near_geometry_of_deep_balance (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r k:ℕ) (ηcover ell b₀ c₀ deep:ℝ) (hell:0≤ell) (hTX:T⊆X) (hWZ:W⊆Z)
    (D:OrdinaryRootCoverNonrootData Q F H X T Z W r ηcover ell)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hdeep:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep)
    (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤b₀)
    (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤c₀)
    (ω βparent β b B εparent εstar η ξ ζ p ε f binner c:ℝ)
    (hf:deep+3*ell≤f)
    (hb:b₀+3*ell+(deep+3*ell)≤binner)
    (hc:c₀+3*ell+(deep+3*ell)≤c):
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    let Q':=Q\D.rim;let H':=fun v u=>H v u∧¬D.spokes v u;
    ∀(σ:Sym2 (A⊕C)→Bool),
    OrdinaryNonrootGeometryMargins r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c
      (Q'.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:C)=>H' v.val u.val) Xf Zf σ→
    OrdinaryUnreservedNearGeometryData r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c
      (Q'.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:C)=>H' v.val u.val) Xf Zf σ:=by
  intro A C Xf Zf Q' H' σ m
  have hp:=ordinary_root_cover_deep_balance_profiles Q F H X T Z W r ηcover ell b₀ c₀ deep hell hTX hWZ D hbal hdiv hdeep hinner hcross
  refine ⟨m.positive_V,m.positive_U,m.hub_lower,m.hub_upper,m.xi_nonneg,m.zeta_nonneg,m.p_nonneg,
    m.b_pos,m.B_nonneg,m.k_lower,?_,?_,?_,m.reserve_good,m.inner_rim_size,m.inner_hub_size_V,
    m.inner_hub_size_U,m.reserve_scale_V,m.reserve_scale_U,m.degree_margin,m.isolator_margin,
    m.transfer_margin,m.weight_margin,m.balance_margin⟩
  · intro v
    convert (hp.1 v).trans hf using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v
    convert (hp.2.1 v).trans hb using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv
    convert (hp.2.2 v hv).trans hc using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
