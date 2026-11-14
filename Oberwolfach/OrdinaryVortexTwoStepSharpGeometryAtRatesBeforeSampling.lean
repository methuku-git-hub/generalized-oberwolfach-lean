module

public import Oberwolfach.OrdinaryVortexTwoStepSharpGeometryFromRatesBeforeSampling

@[expose] public section
/-! Name the simultaneous local geometry supplied by one fixed scale choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryVortexTwoStepSharpGeometryAtRatesBeforeSampling
    (mWheel d k:ℕ) (β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh pH εR εH:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout:ℝ):Prop :=
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
    (W.card:ℝ)≤(βh/2)*Fintype.card (Vloc⊕Uloc) ∧
    0≤deep ∧ 0≤bin ∧ 0≤cin ∧
    OrdinaryNonrootGeometryStatic (mWheel+1) k (ρ₀/16) βparent βout b B εparent (εparent+gap)
      ηpack ξreserve ζout p εout fout binner cross Xf Zf ∧
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card A ∧
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card C
end Oberwolfach
