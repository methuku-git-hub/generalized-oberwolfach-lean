module

public import Oberwolfach.OrdinaryAsymmetricParentMarginWithInitialStatic
public import Oberwolfach.OrdinaryAsymmetricSampledCoverGeometryHierarchyGeneralLoad

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_asymmetric_parent_margin_hierarchy_initial_static
    (mWheel loadK d k:ℕ) (hk:4≤k) (ρ₀ βparent b B εparent gap cap δcut:ℝ)
    (hρ₀:0<ρ₀) (hβparent:0<βparent) (hb:0<b) (hB:0≤B) (hgap:0<gap) (hcap:0<cap) (hδcut:0<δcut):
    ∃βout ξreserve ζout edit:ℝ,0<βout ∧ βout=βparent/2 ∧ 0<ξreserve ∧ 0<ζout ∧ 0<edit ∧ ξreserve≤cap ∧ ζout≤cap ∧
    ∀root eParent hParent εcap ζh ζe γ:ℝ,0<root→0<eParent→0<hParent→0<εcap→0<ζh→0<ζe→0<γ→γ≤eParent→
    ∃cMatch eCleanup hCleanup:ℝ,0<cMatch ∧ 0<eCleanup ∧ 0<hCleanup ∧
      eCleanup=eParent/2 ∧ hCleanup=hParent/2 ∧
      cMatch≤min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2 ∧
    ∃lam ε βe βh θmatch:ℝ,βe=eCleanup*ε ∧ βh=hCleanup*ε ∧ 0<βe ∧ 0<βh ∧
      0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧ lam≤βe/4 ∧ lam≤βh/2 ∧
      3*(((loadK:ℝ)+1)*lam)≤edit/4 ∧ lam*((mWheel:ℝ)+1)≤edit/4 ∧
      0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ ε≤ξreserve/2 ∧ ε≤ξreserve*(ρ₀/8)/2 ∧ 2*ε^2≤lam ∧
      θmatch=cMatch*ε ∧ 0<θmatch ∧
    ∀rate pcap:ℝ,0<rate→0<pcap→
    ∃ellCap kcap pbound pbar:ℝ,ellCap=θmatch/64 ∧ 0<ellCap ∧ 0<kcap ∧ 0<pbound ∧ pbound≤pcap ∧
      0<pbar ∧ pbar≤1 ∧ pbar≤pbound ∧
    ∀p:ℝ,0<p→p≤pbar→∀othercap:ℝ,0<othercap→∃εsup finishCap δsample loadCap:ℝ,0<p ∧ p≤pbound ∧ p≤1 ∧ p≤4*θmatch ∧
      20*Real.sqrt (2*p)≤θmatch/2 ∧ 0<εsup ∧ εsup≤p^2/4 ∧
      0<finishCap ∧ finishCap≤othercap ∧ finishCap≤ellCap ∧ 0<δsample ∧ 0<loadCap ∧ loadCap≤1 ∧ loadCap≤finishCap ∧
      (∀n ηrate ellrate:ℝ,0≤n→ηrate≤ellCap→ellrate≤ellCap→
        βe*n+3*max (ηrate*n) (ellrate*n)≤(eParent*ε)*n ∧
        βh*n+2*(ellrate*n)≤(hParent*ε)*n) ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤finishCap→ν≤finishCap→η≤finishCap→ell≤ellCap→
        τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤θmatch*p/4 ∧ ν+η≤θmatch*p/4) ∧
      (∀ν:ℝ,0≤ν→ν≤finishCap→∃N:ℕ,∀n:ℕ,N≤n→
        2≤θmatch*p*n/4 ∧ ∃K Dmax:ℕ,0<K ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤kcap^2*n ∧
        ∀(Lconf t η:ℝ),Lconf≤kcap^2*n→t≤ν*n→0≤η→η≤finishCap→
          ((n*Dmax*(mWheel+1):ℕ):ℝ)/(K:ℝ)+
            (((mWheel+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((K+Dmax:ℕ):ℝ))+
            (Dmax:ℝ)+((Dmax*(mWheel+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*t ∧
          ν*n+η*n+2*((2*p)*n)+((3*(K+Dmax)+Dmax*(mWheel+1):ℕ):ℝ)≤rate*n) ∧
    ∀ηpack:ℝ,0<ηpack→∃εout γgeom aLoad ξroot η₀ ηbal ηInitial βcap δcap:ℝ,
      0<εout ∧ εout≤1 ∧ 0<γgeom ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤loadCap ∧ aLoad≤γgeom/1000 ∧
      aLoad≤edit/(72*((mWheel:ℝ)+2)) ∧ ξroot=min (ε/200) (aLoad^2/160) ∧
      0<ξroot ∧ ξroot≤ε/100 ∧ ξroot≤γgeom/160000 ∧ 80*ξroot≤aLoad^2 ∧
      max (18*aLoad+3*(((loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((mWheel:ℝ)+1))≤ellCap ∧ 10*ξroot≤finishCap ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γgeom/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ 0<βcap ∧ βcap≤1/4 ∧ βcap≤γgeom/1000 ∧ 0<δcap ∧ δcap≤γgeom/1000 ∧
    OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (mWheel+1) k 2 ρ₀ βparent b B εparent gap
      βout ξreserve ζout edit p ηpack εout γgeom ∧
    ∀(β εR εH pH:ℝ),0≤β→β≤βcap→0≤εR→εR≤δcap→0≤εH→εH≤δcap→0≤pH→pH≤1→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh pH εR εH
        βparent b B εparent gap βout ζout ηpack εout :=by
  obtain ⟨βout,ξreserve,ζout,edit,hβout,hβeq,hξreserve,hζout,hedit,hξcap,hζcap,hgeom⟩:=
    ordinary_vortex_buffered_root_static_geometry_separate_at_scale_choice (mWheel+1) k 2 (by omega)
      ρ₀ βparent b B εparent gap cap hk hρ₀ hβparent hb hB hgap hcap
  refine ⟨βout,ξreserve,ζout,edit,hβout,hβeq,hξreserve,hζout,hedit,hξcap,hζcap,?_⟩
  exact ordinary_asymmetric_parent_margin_with_initial_static mWheel loadK d k ρ₀ βparent b B εparent gap δcut
    βout ξreserve ζout edit hρ₀ hδcut hξreserve hedit hgeom
end Oberwolfach
