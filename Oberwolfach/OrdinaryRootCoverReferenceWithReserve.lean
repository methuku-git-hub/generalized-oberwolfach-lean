module

public import Oberwolfach.OrdinaryRootCoverReferenceData

@[expose] public section
/-! Add the actual sampled reserve to the selected root-cover reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_root_cover_reference_with_reserve (P Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r k:ℕ) (hr:3≤r) (ηcover ell b₀ c₀:ℝ)
    (D:OrdinaryRootCoverNonrootData Q F H X T Z W r ηcover ell)
    (α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c:ℝ)
    (d:OrdinaryRootCoverReferenceData P Q F H X T Z W r k hr ηcover ell b₀ c₀ D
      α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c):
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:C↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    let Q':=Q\D.rim;let H':=fun v u=>H v u∧¬D.spokes v u;
    let Df:=(ordinaryPhysicalGraph D.rim D.spokes).comap (φ.sumMap ψ);
    ∀σ:Sym2 (A⊕C)→Bool,
    OrdinaryBoundaryReserveGood (Q'.induce (A:Set V)) (fun (v:A) (u:C)=>H' v.val u.val) Xf Zf p ε σ→
    Nonempty (OrdinaryPreCoverPackingInputs r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c ell
      (P.induce (A:Set V)) (Q.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:C)=>H v.val u.val) Xf Zf Df σ):=by
  intro A C φ ψ Xf Zf Q' H' Df σ hgood
  have m:=ordinary_nonroot_geometry_with_reserve r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c
    (Q'.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:C)=>H' v.val u.val) Xf Zf σ d.static (by
      convert hgood using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  exact ordinary_root_cover_precover_inputs P Q F H X T Z W r k hr ηcover ell b₀ c₀ d.ell_nonneg D
    d.graph_sub d.balance d.divisible d.inner_balance d.cross_balance α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c
    d.full_margin d.inner_margin d.cross_margin σ d.fields m d.scale_V d.scale_U
end Oberwolfach
