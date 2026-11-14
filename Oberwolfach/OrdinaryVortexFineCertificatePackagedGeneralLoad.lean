module

public import Oberwolfach.OrdinaryVortexFineCertificateAtGeneralLoad
public import Oberwolfach.OrdinaryVortexAsymmetricPairingGeometryProp
public import Oberwolfach.OrdinaryAsymmetricCertificateFromSharpReference
public import Oberwolfach.OrdinaryAsymmetricCertificateFromSharpCapacity
public import Oberwolfach.OrdinaryRootFirstRootFreeSharpReferencePerHostSampledCover

@[expose] public section
/-! A fixed sharp root reference supplies the cleanup probability used by
the asymmetric per-host certificate, on the same physical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_fine_certificate_packaged_general_load
    (m loadK:ℕ) (hm:3≤m) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β bRoot BRoot hpack δ:ℝ,
      0<ω→0<β→0<bRoot→0<BRoot→0<hpack→0<δ→δ<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
    ∀(γ bHub BHub p₀ κ:ℝ),0<γ→0<bHub→0≤BHub→0<p₀→p₀≤1→0<κ→κ≤1→
    ∃ηhub ζhub a ηend ζlocal δend:ℝ,
      0<ηhub ∧ 0<ζhub ∧ 0<a ∧ a≤1 ∧ 0<ηend ∧ 0<ζlocal ∧ 0<δend ∧
    ∀(b₀:ℕ) (p βe βh ν cap εsup δsample:ℝ),
      0<p→p≤1→0<βe→0<βh→0<ν→0<cap→0<εsup→0<δsample→
    ∃τ:ℝ,τ=ordinarySafeCleanupScale (m+1) p βe (βh/2) ν (min cap 1) ∧ 0<τ ∧ τ≤cap ∧ τ≤1 ∧
    ∀L:ℝ,0≤L→∃ηpack:ℝ,0<ηpack ∧ cLinear*τ≤ηpack ∧ ∃n₀ Nclean:ℕ,
    ∀εgeom:ℝ,0<εgeom→∃Nreserve Ncert:ℕ,
    OrdinaryVortexFineCertificateAtGeneralLoad {m:=m, k:=k, loadK:=loadK, hm:=hm, α:=α, ω:=ω, β:=β, bRoot:=bRoot, BRoot:=BRoot, hpack:=hpack, δ:=δ, εstar:=εstar, ηpack:=ηpack, γ:=γ, bHub:=bHub, BHub:=BHub, p₀:=p₀, κ:=κ, ηhub:=ηhub, ζhub:=ζhub, ζlocal:=ζlocal, δend:=δend, b₀:=b₀, p:=p, βe:=βe, βh:=βh, ν:=ν, cap:=cap, εsup:=εsup, δsample:=δsample, τ:=τ, L:=L, n₀:=n₀, Nclean:=Nclean, εgeom:=εgeom, Nreserve:=Nreserve, Ncert:=Ncert}:=by
  obtain ⟨Nroot,hroot⟩:=ordinary_vortex_fine_cover_certificate_from_schedule_general_load m loadK hm α hα
  refine ⟨Nroot,?_⟩
  intro k hk ω β bRoot BRoot hpack δ hω hβ hbRoot hBRoot hhpack hδ hδ1
  obtain ⟨εstar,cLinear,hεstar,hcLinear,hroot⟩:=hroot k hk ω β bRoot BRoot hpack δ hω hβ hbRoot hBRoot hhpack hδ hδ1
  refine ⟨εstar,cLinear,hεstar,hcLinear,?_⟩
  intro γ bHub BHub p₀ κ hγ hbHub hBHub hp₀ hp₀1 hκ hκ1
  obtain ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,hroot⟩:=
    hroot γ bHub BHub p₀ κ hγ hbHub hBHub hp₀ hp₀1 hκ hκ1
  refine ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,?_⟩
  intro b₀ p βe βh ν cap εsup δsample hp hp1 hβe hβh hν hcap hsup hδsample
  obtain ⟨τ,hτeq,hτ,hτcap,hτ1,hroot⟩:=hroot b₀ p βe βh ν cap εsup δsample hp hp1 hβe hβh hν hcap hsup hδsample
  refine ⟨τ,hτeq,hτ,hτcap,hτ1,?_⟩
  intro L hL
  obtain ⟨ηpack,hηpack,hlinear,n₀,Nclean,hroot⟩:=hroot L hL
  refine ⟨ηpack,hηpack,hlinear,n₀,Nclean,?_⟩
  intro εgeom hεgeom
  obtain ⟨Nreserve,Ncert,hroot⟩:=hroot εgeom hεgeom
  refine ⟨Nreserve,Ncert,?_⟩
  dsimp only [OrdinaryVortexFineCertificateAtGeneralLoad]
  exact hroot
end Oberwolfach
