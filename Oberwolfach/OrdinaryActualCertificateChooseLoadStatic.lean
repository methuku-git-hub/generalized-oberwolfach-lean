module

public import Oberwolfach.OrdinaryActualCertificateChosenLoadStaticAt
public import Oberwolfach.OrdinaryActualCertificateAfterRateStaticAt

@[expose] public section
/-! The certificate's load is selected under the very deep-cover cap that
was fixed before the common event and the certificate rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_certificate_choose_load_static
    (mWheel loadK k:ℕ) (hm:3≤mWheel) (α βparent ω bRoot BRoot hpack δ εstar cLinear:ℝ)
    (ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γ bHub BHub p₀ κ ηhub ζhub ζlocal δend:ℝ)
    (eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate pcap:ℝ)
    (ha:0<a) (hpcap:0<pcap)
    (hafter:OrdinaryActualCertificateAfterRateStaticAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
      ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γ bHub BHub p₀ κ ηhub ζhub ζlocal δend eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate):
    OrdinaryActualCertificateChosenLoadStaticAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
      ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γ bHub BHub p₀ κ ηhub ζhub ζlocal δend eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate pcap :=by
  have hPreparedBulkChunks :=
    hafter pcap a hpcap ha
  obtain ⟨ellCap,kcap,pbound,p,εsup,finishCap,δsample,loadCap,ν,cap,hellEq,hell,hPreparedBulkChunksRest1⟩:=hPreparedBulkChunks
  obtain ⟨hkcap,hpbound,hpcap',hp,hpp,hp1,hpθ,hsqrt,hεsup,hεsupcap,hfinish,hfinishA,hPreparedBulkChunksRest2⟩:=hPreparedBulkChunksRest1
  obtain ⟨hfinishell,hδsample,hload,hload1,hloadfinish,hν,hcap,hνfinish,hcapfinish,Nfinish,hschedule,τ,hPreparedBulkChunksRest3⟩:=hPreparedBulkChunksRest2
  obtain ⟨ηpack,hτeq,hτ,hτcap,hτ1,hηpack,hlinear,n₀,εout,γgeom,aLoad,ξroot,hPreparedBulkChunksRest4⟩:=hPreparedBulkChunksRest3
  obtain ⟨η₀,ηbal,ηInitial,βcap,δcap,δInitial,δedit,ηedit,hεout,hεout1,hγgeom,haLoad,hPreparedBulkChunksRest5⟩:=hPreparedBulkChunksRest4
  obtain ⟨haLoad1,haLoadCap,haLoadγ,haLoadEdit,hξeq,hξ,hξε,hξγ,hξsq,hellRate,hcoverRate,hηeq,hPreparedBulkChunksRest6⟩:=hPreparedBulkChunksRest5
  obtain ⟨hη₀,hηbal,hηbal₀,hηbalγ,hηInitial,hηInitialBal,hβcap,hβcap1,hβcapγ,hδcap,hδcapγ,hδInitial,hPreparedBulkChunksRest7⟩:=hPreparedBulkChunksRest6
  obtain ⟨hδInitialα,hδInitialη,hδedit,hδeditα,hδeditη,hηedit,hstatic,hremain⟩:=hPreparedBulkChunksRest7
  have haLoadA:aLoad≤a:=haLoadCap.trans (hloadfinish.trans hfinishA)
  exact ⟨ellCap,kcap,pbound,p,εsup,finishCap,δsample,loadCap,ν,cap,
    hellEq,hell,hkcap,hpbound,hpcap',hp,hpp,hp1,hpθ,hsqrt,hεsup,hεsupcap,hfinish,hfinishA,hfinishell,
    hδsample,hload,hload1,hloadfinish,hν,hcap,hνfinish,hcapfinish,
    Nfinish,hschedule,τ,ηpack,hτeq,hτ,hτcap,hτ1,hηpack,hlinear,
    n₀,εout,γgeom,aLoad,ξroot,η₀,ηbal,ηInitial,βcap,δcap,δInitial,δedit,ηedit,
    hεout,hεout1,hγgeom,haLoad,haLoad1,haLoadCap,haLoadA,haLoadγ,haLoadEdit,hξeq,hξ,hξε,hξγ,hξsq,
    hellRate,hcoverRate,hηeq,hη₀,hηbal,hηbal₀,hηbalγ,hηInitial,hηInitialBal,hβcap,hβcap1,hβcapγ,
    hδcap,hδcapγ,hδInitial,hδInitialα,hδInitialη,hδedit,hδeditα,hδeditη,hηedit,hstatic,hremain⟩
end Oberwolfach
