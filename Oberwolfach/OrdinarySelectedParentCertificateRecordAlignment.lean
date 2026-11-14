module

public import Oberwolfach.OrdinarySelectedParentCertificateParameters

@[expose] public section
/-! The record produced by the original parent selector is the literal
record used simultaneously by the initial and later wheel certificates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_selected_parent_certificate_record_alignment
    (mWheel loadK k d n₀ Nclean Nreserve Ncert:ℕ) (hm:3≤mWheel)
    (α ρ₀ pstar βout cParent Bhost hParent δparent εparent gapParent geomGap εstar:ℝ)
    (ηpack γcert b Bweight κ ηHub ζhub ζlocal δend:ℝ)
    (p βe βh ν cap εsup δsample τ εout:ℝ)
    (hεstar:εstar=(εparent+gapParent)+geomGap):
    ({m:=mWheel, k:=k, loadK:=loadK, hm:=hm, α:=α, ω:=ρ₀/16, β:=βout,
      bRoot:=cParent*(1-δparent)^((mWheel+1)-1), BRoot:=Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1)),
      hpack:=hParent/2, δ:=δparent/2, εstar:=εstar, ηpack:=ηpack, γ:=γcert,
      bHub:=b, BHub:=Bweight, p₀:=pstar, κ:=κ, ηhub:=ηHub, ζhub:=ζhub, ζlocal:=ζlocal,
      δend:=δend, b₀:=2*(3*d), p:=p, βe:=βe, βh:=βh, ν:=ν, cap:=cap, εsup:=εsup,
      δsample:=δsample, τ:=τ, L:=((2*(3*d):ℕ):ℝ), n₀:=n₀, Nclean:=Nclean, εgeom:=εout,
      Nreserve:=Nreserve, Ncert:=Ncert}:OrdinaryVortexFineCertificateParametersGeneralLoad)=
    ordinarySelectedParentCertificateParameters mWheel loadK k d n₀ Nclean Nreserve Ncert hm
      α ρ₀ pstar βout cParent Bhost hParent δparent εparent gapParent geomGap
      ηpack γcert b Bweight pstar κ ηHub ζhub ζlocal δend p βe βh ν cap εsup δsample τ εout :=by
  simp only [ordinarySelectedParentCertificateParameters,Nat.add_sub_cancel,hεstar]
end Oberwolfach
