module

public import Oberwolfach.OrdinaryVortexInitialFineSharpGeometryGeneralLoad
public import Oberwolfach.OrdinaryInitialGeometryFromBalanceMargin

@[expose] public section
/-! Static sharp geometry at the first parent, with the actual initial
correction charged directly to its common edit bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_initial_geometry_from_balance_margin
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
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*J.card)+3*L≤η*I.card→
    (T.card:ℝ)+W.card≤lam*Fintype.card Vloc ∧
    (T.card:ℝ)≤(βe/4)*Fintype.card (Vloc⊕Uloc) ∧
    (W.card:ℝ)≤(βh/2)*Fintype.card (Vloc⊕Uloc) ∧
    0≤deep ∧ 0≤bin ∧ 0≤cin ∧
    OrdinaryNonrootGeometryStatic (mWheel+1) k (ρ₀/16) βparent βout b B εparent (εparent+gap)
      ηpack ξreserve ζout p εout fout binner cross Xf Zf ∧
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card A ∧
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card C:=by
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q Vloc Uloc I T J W A C Xf Zf deep cover loss bin cin ell fout binner cross hmargin
  have hLcap:=ordinary_initial_geometry_from_balance_margin I J (initialIndexDensity U D*pH) β εR εH L η γ
    (mul_nonneg (le_trans hρ₀.le hρlo) hpH) hβ hεR hεH hη hηcap hmargin
  exact ordinary_vortex_initial_fine_sharp_geometry_general_load mWheel loadK k β ε ρ₀ lam ξreserve ξroot κ η γ edit p βe βh pH εR εH L
    βparent b B εparent gap βout ζout ηpack εout hgeometry hβ hβ1 hε hρ₀ hγ hlam hlam1 hlamρ
    hξreserve hεξ hερ hεroot hβe hβh hpH hpH1 hεR hεH hξroot hκ hη hL hedit hβcap hRcap hHcap
    hξcap hκcap hηcap hrow hlevel hκedit hTcap hWcap V U P D m hreg hn hD hρlo hρhi hm Q hLcap
end Oberwolfach
