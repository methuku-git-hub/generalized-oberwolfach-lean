module

public import Oberwolfach.MarkedFixedVortexParentDegrees
public import Oberwolfach.MarkedVortexActiveDegreeFields
public import Oberwolfach.MarkedVortexFirstActiveRelativeSize
public import Oberwolfach.FirstVortexHostScaleToInner

@[expose] public section
/-! Instantiate the parent and first-active degree scales from the original
regular host and the actual vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_parent_active_degree_inputs
    {n D m:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (β ε α:ℝ) (Q:Vortex U P D β ε m)
    (hreg:P.IsRegularOfDegree D) (hn:0<n)
    (hD:(1/2+α)*(n:ℝ)≤D) (hα:0<α) (hρ:0< initialIndexDensity U D)
    (hβ:0≤β) (hβα:β≤α/8) (hβstrong:β≤3*α/40) (hβ1:β≤3/20)
    (hε:0<ε) (hε1:ε≤1/4) (hm:0<m):
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let A:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))
    let B:Finset (markedVortexHubType Q 1):=Finset.univ\markedVortexInnerHubs Q 1;
    0<Fintype.card A ∧
    (Fintype.card W:ℝ)/2≤2*(Fintype.card Z:ℝ)/initialIndexDensity U D ∧
    2*(Fintype.card Z:ℝ)/initialIndexDensity U D≤2*Fintype.card W ∧
    (Fintype.card A:ℝ)/2≤2*(B.card:ℝ)/initialIndexDensity U D ∧
    2*(B.card:ℝ)/initialIndexDensity U D≤2*Fintype.card A :=by
  intro W Z A B
  have hFirst:=vortex_first_inner_positive_from_terminal Q hε hm
  have hFirstR:(1:ℝ)≤(Q.extendedVertices 1).card:=by exact_mod_cast hFirst
  have heq:instDecidableEqFin n=(fun a b:Fin n=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  have hActive:=marked_vortex_first_active_relative_size P D m β ε Q hε.le hε1
  try rw [←heq] at hActive
  have hActivePos:(0:ℝ)<Fintype.card A:=by
    change (3/4:ℝ)*(Q.extendedVertices 1).card≤(Fintype.card A:ℝ) at hActive
    nlinarith
  have hActiveNat:0<Fintype.card A:=by exact_mod_cast hActivePos
  let x:A:=Classical.choice (Fintype.card_pos_iff.mp hActiveNat)
  have hn':0<Fintype.card (Fin n):=by simpa using hn
  have hD':(1/2+α)*Fintype.card (Fin n)≤(D:ℝ):=by simpa only [Fintype.card_fin] using hD
  have hParent:=marked_vortex_fixed_parent_degree_fields Q hreg hn' hD' hα hρ hβ hβα (by linarith) hε hm 0 Q.length_pos
  have hActiveDegree:=marked_vortex_active_degree_fields Q hreg hn' hD' hα hρ hβ hβstrong hβ1 hε.le hε1 1 (by
    refine ⟨x.val,?_⟩
    simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and] using x.property)
  have hActiveLo:=hActiveDegree.1
  have hActiveHi:=hActiveDegree.2.1
  rw [←heq] at hActiveLo hActiveHi
  refine ⟨hActiveNat,hParent.2.2.1,hParent.2.2.2,?_,?_⟩
  · simpa only [A,B,Fintype.card_coe] using hActiveLo
  · simpa only [A,B,Fintype.card_coe] using hActiveHi
end Oberwolfach
