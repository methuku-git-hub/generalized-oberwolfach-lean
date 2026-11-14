module

public import Oberwolfach.OrdinarySharpGeometryMarginsOnFiniteHost
public import Oberwolfach.OrdinaryFineDeepCostSchedule
public import Oberwolfach.OrdinaryVortexFineConflictSizeThreshold
public import Oberwolfach.OrdinaryVortexBufferedRootRestrictionGeometry
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! On every later parent, the original vortex geometry and the fine
protected-boundary cost supply the sharp numerical margins uniformly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_two_step_sharp_geometry_margins
    (mWheel d:ℕ) (β ε ρ₀ lam ξreserve ξroot κ η ηInitial γ edit p βe βh pH εR εH:ℝ)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hγ:0<γ)
    (hlam:0≤lam) (hlam1:lam≤1/4) (hlamρ:lam≤(ρ₀/8)/2)
    (hξreserve:0≤ξreserve) (hεξ:ε≤ξreserve/2) (hερ:ε≤ξreserve*(ρ₀/8)/2) (hεroot:2*ε^2≤lam)
    (hβe:0≤βe) (hβh:0≤βh) (hp:0≤p) (hpH:0≤pH) (hpH1:pH≤1)
    (hεR:0≤εR) (hεH:0≤εH) (hξroot:0≤ξroot) (hκ:0≤κ) (hη:0≤η) (hηI:0≤ηInitial)
    (hedit:0<edit) (hβcap:β≤γ/1000) (hRcap:εR≤γ/1000) (hHcap:εH≤γ/1000)
    (hξcap:ξroot≤γ/160000) (hκcap:κ≤γ/1000) (hηcap:η≤γ/1000) (hηIcap:ηInitial≤η)
    (hrow:3*lam≤edit/4) (hlevel:lam*((mWheel:ℝ)+1)≤edit/4)
    (hκedit:κ≤edit/(72*((mWheel:ℝ)+2)))
    (hTcap:lam≤βe/4) (hWcap:lam≤(p^2*βh/2)/2):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (i:ℕ),i+1<Q.length→
    let Vloc:=markedVortexVertexType Q (i+1);let Uloc:=markedVortexHubType Q (i+1);
    let I:=markedVortexInnerVertices Q (i+1);let T:=ordinaryVortexBufferedVertices Q (i+1) 2;
    let W:=ordinaryVortexBufferedHubs Q (i+1) 2;let A:=Finset.univ\T;
    let deepCost:=ordinaryFineDeepCost Q ξroot i;
    let deep:ℝ:=(initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+
      3*(2*((3*d:ℕ):ℝ))+2*deepCost;
    let cover:=10*ξroot*I.card;let loss:=12*κ*Fintype.card Vloc;
    let bin:=η*I.card;let cin:=ηInitial*I.card+2*deepCost;
    let ell:=max (18*κ*Fintype.card Vloc+3*((W.card:ℝ)+T.card))
      (3*κ*Fintype.card Vloc*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    (T.card:ℝ)+W.card≤lam*Fintype.card Vloc ∧
    (T.card:ℝ)≤(βe/4)*Fintype.card (Vloc⊕Uloc) ∧
    (W.card:ℝ)≤((p^2*βh/2)/2)*Fintype.card (Vloc⊕Uloc) ∧
    0≤deep ∧ 0≤bin ∧ 0≤cin ∧
    deep+2*cover≤γ*Fintype.card A ∧ bin+deep+4*cover≤γ*Fintype.card A ∧
    cin+deep+loss≤γ*Fintype.card A ∧ ell≤edit*Fintype.card A:=by
  obtain ⟨m₀,hm₀,hconf⟩:=ordinary_vortex_fine_conflict_size_threshold β ε ρ₀ (γ/1000) d hβ hβ1 hε hε1 hρ₀ (by positivity)
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q i hi Vloc Uloc I T W A deepCost deep cover loss bin cin ell
  have hmpos:0<m:=by omega
  have hgeo:=ordinary_vortex_buffered_root_restriction_geometry 2 (by omega) P D m β ε ρ₀ lam ξreserve Q hreg hn hD hρ₀
    hρlo hρhi hβ hβ1 hε hmpos hξreserve hlam hlam1 hlamρ hεξ hερ hεroot (i+1) hi
  have hroots:(T.card:ℝ)+W.card≤lam*Fintype.card Vloc:=hgeo.1
  have hU:Fintype.card Uloc≤Fintype.card Vloc:=
    (marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε hmpos (i+1) hi).2.2
  have hq0:0≤ initialIndexDensity U D*pH:=mul_nonneg (le_trans hρ₀.le hρlo) hpH
  have hq1:initialIndexDensity U D*pH≤1:=by
    have hh:=mul_le_mul hρhi hpH1 hpH (by positivity:0≤(1:ℝ))
    simpa using hh
  have hconfCap:3*(2*((3*d:ℕ):ℝ))≤(γ/1000)*Fintype.card Vloc:=hconf V U P D m hreg hn hD hρlo hρhi hm Q (i+1) hi
  have hdeep0:0≤deepCost:=ordinary_fine_deep_cost_nonneg Q ξroot hξroot i
  have hdeepCap:deepCost≤10*ξroot*Fintype.card Vloc:=by dsimp [deepCost,ordinaryFineDeepCost,Vloc];exact le_rfl
  have hnum:=ordinary_sharp_geometry_margins_on_finite_host mWheel I T W (initialIndexDensity U D*pH) β εR εH
    (3*(2*((3*d:ℕ):ℝ))) deepCost ξroot κ η ηInitial γ edit lam hU hq0 hq1 hβ hεR hεH (by positivity) hdeep0
    hξroot hκ hη hηI hγ.le hedit hlam hlam1 hβcap hRcap hHcap hconfCap hξcap hκcap hηcap hηIcap hdeepCap
    hroots hrow hlevel hκedit
  have hcard:=ordinary_root_free_cleanup_card_margins T W lam p βe βh hlam hp hβe hβh hroots hTcap hWcap
  exact ⟨hroots,hcard.1,hcard.2,hnum⟩
end Oberwolfach
