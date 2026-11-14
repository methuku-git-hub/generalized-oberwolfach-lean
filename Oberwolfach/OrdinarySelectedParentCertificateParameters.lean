module

public import Oberwolfach.OrdinaryVortexFineCertificateAtGeneralLoad

@[expose] public section
/-! The literal certificate record selected by the parent hierarchy, with
its root weights, packing slack and cleanup rates named in one place. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def ordinarySelectedParentCertificateParameters
    (mWheel loadK k d n₀ Nclean Nreserve Ncert:ℕ) (hm:3≤mWheel)
    (α ρ₀ pstar βout cParent Bhost hParent δparent εparent gapParent geomGap:ℝ)
    (ηpack γcert b Bweight pmin κ ηHub ζhub ζlocal δend:ℝ)
    (p βe βh ν cap εsup δsample τ εout:ℝ):OrdinaryVortexFineCertificateParametersGeneralLoad :=
  {m:=mWheel, k:=k, loadK:=loadK, hm:=hm, α:=α, ω:=ρ₀/16, β:=βout,
   bRoot:=cParent*(1-δparent)^mWheel, BRoot:=Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1)),
   hpack:=hParent/2, δ:=δparent/2, εstar:=(εparent+gapParent)+geomGap,
   ηpack:=ηpack, γ:=γcert, bHub:=b, BHub:=Bweight, p₀:=pmin, κ:=κ,
   ηhub:=ηHub, ζhub:=ζhub, ζlocal:=ζlocal, δend:=δend, b₀:=2*(3*d),
   p:=p, βe:=βe, βh:=βh, ν:=ν, cap:=cap, εsup:=εsup, δsample:=δsample,
   τ:=τ, L:=((2*(3*d):ℕ):ℝ), n₀:=n₀, Nclean:=Nclean, εgeom:=εout,
   Nreserve:=Nreserve, Ncert:=Ncert}
end Oberwolfach
