module

public import Oberwolfach.OrdinaryVortexTwoStepSharpGeometryFromRatesGeneralLoad

@[expose] public section
/-! Static sharp geometry at the first parent, with the actual initial
correction charged directly to its common edit bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_initial_fine_sharp_geometry_general_load
    (mWheel loadK k:ℕ) (β ε ρ₀ lam ξreserve ξroot κ η γ edit p βe βh pH εR εH L:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout:ℝ)
    (hgeometry:OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (mWheel+1) k 2 ρ₀ βparent b B εparent gap
      βout ξreserve ζout edit p ηpack εout γ)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hρ₀:0<ρ₀) (hγ:0<γ)
    (hlam:0≤lam) (hlam1:lam≤1/4) (hlamρ:lam≤(ρ₀/8)/2)
    (hξreserve:0≤ξreserve) (hεξ:ε≤ξreserve/2) (hερ:ε≤ξreserve*(ρ₀/8)/2) (hεroot:2*ε^2≤lam)
    (hβe:0≤βe) (hβh:0≤βh) (hpH:0≤pH) (hpH1:pH≤1)
    (hεR:0≤εR) (hεH:0≤εH) (hξroot:0≤ξroot) (hκ:0≤κ) (hη:0≤η) (hL:0≤L)
    (hedit:0<edit) (hβcap:β≤γ/1000) (hRcap:εR≤γ/1000) (hHcap:εH≤γ/1000)
    (hξcap:ξroot≤γ/160000) (hκcap:κ≤γ/1000) (hηcap:η≤γ/1000)
    (hrow:3*(((loadK:ℝ)+1)*lam)≤edit/4) (hlevel:lam*((mWheel:ℝ)+1)≤edit/4)
    (hκedit:κ≤edit/(72*((mWheel:ℝ)+2))) (hTcap:lam≤βe/4) (hWcap:lam≤βh/2):
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0<m→
    ∀(Q:Vortex U P D β ε m),
    let Vloc:=markedVortexVertexType Q 0;let Uloc:=markedVortexHubType Q 0;
    let I:=markedVortexInnerVertices Q 0;let T:=ordinaryVortexBufferedVertices Q 0 2;
    let J:=markedVortexInnerHubs Q 0;let W:=ordinaryVortexBufferedHubs Q 0 2;
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈I);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈J);
    let deep:ℝ:=(initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+3*L;
    let cover:=10*ξroot*I.card;let loss:=12*κ*Fintype.card Vloc;
    let bin:=η*I.card;let cin:=η*I.card;
    let ell:=max (18*κ*Fintype.card Vloc+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*κ*Fintype.card Vloc*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    let fout:=deep+2*cover;let binner:=bin+deep+4*cover;let cross:=cin+deep+loss;
    3*L≤(γ/1000)*Fintype.card Vloc→
    (T.card:ℝ)+W.card≤lam*Fintype.card Vloc ∧
    (T.card:ℝ)≤(βe/4)*Fintype.card (Vloc⊕Uloc) ∧
    (W.card:ℝ)≤(βh/2)*Fintype.card (Vloc⊕Uloc) ∧
    0≤deep ∧ 0≤bin ∧ 0≤cin ∧
    OrdinaryNonrootGeometryStatic (mWheel+1) k (ρ₀/16) βparent βout b B εparent (εparent+gap)
      ηpack ξreserve ζout p εout fout binner cross Xf Zf ∧
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card A ∧
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card C:=by
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q Vloc Uloc I T J W A C Xf Zf deep cover loss bin cin ell fout binner cross hLcap
  have hgeo:=ordinary_vortex_buffered_root_restriction_geometry 2 (by omega) P D m β ε ρ₀ lam ξreserve Q hreg hn hD hρ₀
    hρlo hρhi hβ hβ1 hε hm hξreserve hlam hlam1 hlamρ hεξ hερ hεroot 0 Q.length_pos
  have hroots:(T.card:ℝ)+W.card≤lam*Fintype.card Vloc:=hgeo.1
  have hU:Fintype.card Uloc≤Fintype.card Vloc:=
    (marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε hm 0 Q.length_pos).2.2
  have hq0:0≤ initialIndexDensity U D*pH:=mul_nonneg (le_trans hρ₀.le hρlo) hpH
  have hq1:initialIndexDensity U D*pH≤1:=by
    have hh:=mul_le_mul hρhi hpH1 hpH (by positivity:0≤(1:ℝ))
    simpa using hh
  have hnum:=ordinary_sharp_geometry_margins_on_finite_host_general_load mWheel loadK I T W (initialIndexDensity U D*pH) β εR εH
    (3*L) 0 ξroot κ η η γ edit lam hU hq0 hq1 hβ hεR hεH (by positivity) (by norm_num)
    hξroot hκ hη hη hγ.le hedit hlam hlam1 hβcap hRcap hHcap hLcap hξcap hκcap hηcap le_rfl
    (by positivity) hroots hrow hlevel hκedit
  have hcard:=ordinary_root_free_cleanup_card_margins_before_sampling T W lam βe βh hlam hβe hβh hroots hTcap hWcap
  have hdeep0:0≤deep:=by dsimp [deep];positivity
  have hbin0:0≤bin:=by dsimp [bin];positivity
  have hcin0:0≤cin:=by dsimp [cin];positivity
  have hcover0:0≤cover:=by dsimp [cover];positivity
  have hloss0:0≤loss:=by dsimp [loss];positivity
  have hf0:0≤fout:=by dsimp [fout];positivity
  have hb0:0≤binner:=by dsimp [binner];positivity
  have hc0:0≤cross:=by dsimp [cross];positivity
  have he0:0≤ell:=by dsimp [ell];positivity
  have hnum':fout≤γ*Fintype.card A ∧ binner≤γ*Fintype.card A ∧ cross≤γ*Fintype.card A ∧ ell≤edit*Fintype.card A:=by
    simpa only [deep,cover,loss,bin,cin,ell,fout,binner,cross,A,Vloc,mul_zero,zero_mul,add_zero] using hnum.2.2.2
  have hg:=hgeometry V U P D m β ε lam Q hreg hn hD hρlo hρhi hβ hβ1 hε hm hlam hlam1 hlamρ hεξ hερ hεroot
    0 Q.length_pos fout binner cross ell hf0 hb0 hc0 he0 hnum'.1 hnum'.2.1 hnum'.2.2.1 hnum'.2.2.2
  exact ⟨hroots,hcard.1,hcard.2,hdeep0,hbin0,hcin0,hg.2⟩
end Oberwolfach
