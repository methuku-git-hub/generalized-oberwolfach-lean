module

public import Oberwolfach.OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale
public import Oberwolfach.OrdinaryVortexTwoStepSharpGeometryMargins

@[expose] public section
/-! The original vortex geometry, the selected fine-cost schedule and the
separately chosen scales imply the actual sharp reference geometry at every
later parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_two_step_sharp_geometry_from_rates
    (mWheel d k:ℕ) (β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh pH εR εH:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout:ℝ)
    (hgeometry:OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (mWheel+1) k 2 ρ₀ βparent b B εparent gap
      βout ξreserve ζout edit p ηpack εout γ)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hγ:0<γ)
    (hlam:0≤lam) (hlam1:lam≤1/4) (hlamρ:lam≤(ρ₀/8)/2)
    (hξreserve:0≤ξreserve) (hεξ:ε≤ξreserve/2) (hερ:ε≤ξreserve*(ρ₀/8)/2) (hεroot:2*ε^2≤lam)
    (hβe:0≤βe) (hβh:0≤βh) (hp:0≤p) (hpH:0≤pH) (hpH1:pH≤1)
    (hεR:0≤εR) (hεH:0≤εH) (hξroot:0≤ξroot) (hκ:0≤κ) (hη:0≤ηbal) (hηI:0≤ηInitial)
    (hedit:0<edit) (hβcap:β≤γ/1000) (hRcap:εR≤γ/1000) (hHcap:εH≤γ/1000)
    (hξcap:ξroot≤γ/160000) (hκcap:κ≤γ/1000) (hηcap:ηbal≤γ/1000) (hηIcap:ηInitial≤ηbal)
    (hrow:3*lam≤edit/4) (hlevel:lam*((mWheel:ℝ)+1)≤edit/4)
    (hκedit:κ≤edit/(72*((mWheel:ℝ)+2))) (hTcap:lam≤βe/4) (hWcap:lam≤(p^2*βh/2)/2):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (i:ℕ),i+1<Q.length→
    let Vloc:=markedVortexVertexType Q (i+1);let Uloc:=markedVortexHubType Q (i+1);
    let I:=markedVortexInnerVertices Q (i+1);let T:=ordinaryVortexBufferedVertices Q (i+1) 2;
    let J:=markedVortexInnerHubs Q (i+1);let W:=ordinaryVortexBufferedHubs Q (i+1) 2;
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈I);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈J);
    let deepCost:=ordinaryFineDeepCost Q ξroot i;
    let deep:ℝ:=(initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+
      3*(2*((3*d:ℕ):ℝ))+2*deepCost;
    let cover:=10*ξroot*I.card;let loss:=12*κ*Fintype.card Vloc;
    let bin:=ηbal*I.card;let cin:=ηInitial*I.card+2*deepCost;
    let ell:=max (18*κ*Fintype.card Vloc+3*((W.card:ℝ)+T.card))
      (3*κ*Fintype.card Vloc*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    let fout:=deep+2*cover;let binner:=bin+deep+4*cover;let cross:=cin+deep+loss;
    (T.card:ℝ)+W.card≤lam*Fintype.card Vloc ∧
    (T.card:ℝ)≤(βe/4)*Fintype.card (Vloc⊕Uloc) ∧
    (W.card:ℝ)≤((p^2*βh/2)/2)*Fintype.card (Vloc⊕Uloc) ∧
    0≤deep ∧ 0≤bin ∧ 0≤cin ∧
    OrdinaryNonrootGeometryStatic (mWheel+1) k (ρ₀/16) βparent βout b B εparent (εparent+gap)
      ηpack ξreserve ζout p εout fout binner cross Xf Zf ∧
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card A ∧
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card C:=by
  obtain ⟨m₀,hm₀,hnum⟩:=ordinary_vortex_two_step_sharp_geometry_margins mWheel d β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh pH εR εH
    hβ hβ1 hε hε1 hρ₀ hγ hlam hlam1 hlamρ hξreserve hεξ hερ hεroot hβe hβh hp hpH hpH1 hεR hεH hξroot hκ hη hηI
    hedit hβcap hRcap hHcap hξcap hκcap hηcap hηIcap hrow hlevel hκedit hTcap hWcap
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q i hi Vloc Uloc I T J W A C Xf Zf deepCost deep cover loss bin cin ell fout binner cross
  have hnumer:=hnum V U P D m hreg hn hD hρlo hρhi hm Q i hi
  change (T.card:ℝ)+W.card≤lam*Fintype.card Vloc ∧
    (T.card:ℝ)≤(βe/4)*Fintype.card (Vloc⊕Uloc) ∧
    (W.card:ℝ)≤((p^2*βh/2)/2)*Fintype.card (Vloc⊕Uloc) ∧
    0≤deep ∧ 0≤bin ∧ 0≤cin ∧ fout≤γ*Fintype.card A ∧ binner≤γ*Fintype.card A ∧
    cross≤γ*Fintype.card A ∧ ell≤edit*Fintype.card A at hnumer
  obtain ⟨hroot,hT,hW,hdeep,hbin,hcin,hf,hbi,hcr,hell⟩:=hnumer
  have hcover:0≤cover:=by dsimp [cover];positivity
  have hloss:0≤loss:=by dsimp [loss];positivity
  have hf0:0≤fout:=by dsimp [fout];positivity
  have hbi0:0≤binner:=by dsimp [binner];positivity
  have hcr0:0≤cross:=by dsimp [cross];positivity
  have hell0:0≤ell:=by dsimp [ell];positivity
  have hg:=hgeometry V U P D m β ε lam Q hreg hn hD hρlo hρhi hβ hβ1 hε (by omega) hlam hlam1 hlamρ hεξ hερ hεroot
    (i+1) hi fout binner cross ell hf0 hbi0 hcr0 hell0 hf hbi hcr hell
  exact ⟨hroot,hT,hW,hdeep,hbin,hcin,hg.2⟩
end Oberwolfach
