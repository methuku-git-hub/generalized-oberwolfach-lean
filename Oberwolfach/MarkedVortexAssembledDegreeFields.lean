module

public import Oberwolfach.MarkedVortexParentLevelDegreeInputs
public import Oberwolfach.MarkedVortexInnerLevelDegreeInputs

@[expose] public section
/-! Parent and inner degree fields with explicit, fixed fractions of the host
minimum-degree margin. The inner estimate holds for every parent vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε α:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_assembled_degree_fields
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(1/2+α)*Fintype.card V≤(D:ℝ)) (hα:0<α)
    (hρ:0 < initialIndexDensity U D) (hb:0≤β) (hbα:β≤α/8)
    (hb1:β≤1/4) (he:0<ε) (hm:0<m) (κ x:ℝ) (hbκ:β≤κ) (hbx:β≤x)
    (L:ℕ) (hL:L<Q.length):
    let gamma:=α/16
    let alphaInner:=α/8;
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let I:=markedVortexInnerVertices Q i
      let J:=markedVortexInnerHubs Q i
      let P:=G.comap (markedVortexVertexEmbedding Q i)
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      let errParent:=β*I.card;
      (∀ v:W,(1/2+gamma/2)*Fintype.card W≤(P.degree v:ℝ)) ∧
      (∀ v:W,|(P.degree v:ℝ)-Dload|≤κ*Fintype.card W) ∧
      (Fintype.card W:ℝ)/2≤Dload ∧ Dload≤2*Fintype.card W ∧
      (∀ v:W,|((P.neighborFinset v∩I).card:ℝ)-2*J.card/initialIndexDensity U D|≤errParent) ∧
      (∀ v:W,(1/2+2*alphaInner)*I.card≤((P.neighborFinset v∩I).card:ℝ)) ∧
      0≤errParent ∧ errParent≤x*Fintype.card W := by
  intro gamma alphaInner i hi W Z I J P Dload errParent
  have hp:=marked_vortex_parent_level_degree_inputs Q hreg hn hD hα hρ hb hbα hb1 he hm κ hbκ L hL i hi
  have hi' := marked_vortex_inner_level_degree_inputs Q hreg hn hD hα hρ hb hbα hb1 he hm
    alphaInner x (by dsimp [alphaInner]; linarith) hbx L hL i hi
  have hg:(1/2+gamma/2:ℝ)≤1/2+α/2 := by dsimp [gamma]; linarith
  refine ⟨?_,hp.2.1,hp.2.2.1,hp.2.2.2,hi'.1,hi'.2.1,?_,hi'.2.2⟩
  · intro v
    exact (mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg _)).trans (hp.1 v)
  · dsimp [errParent]; positivity
end Oberwolfach
