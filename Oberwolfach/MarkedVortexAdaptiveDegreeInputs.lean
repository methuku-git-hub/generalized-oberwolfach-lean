module

public import Oberwolfach.MarkedVortexInnerLevelDegreeInputs
public import Oberwolfach.MarkedVortexParentLevelDegreeInputs

@[expose] public section
/-! The actual vortex supplies the adaptive inner and parent degree inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_adaptive_degree_inputs
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    {G:SimpleGraph V} {D m:ℕ} {β ε α:ℝ} (Q:Vortex U G D β ε m)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(1/2+α)*Fintype.card V≤(D:ℝ)) (hα:0<α)
    (hρ:0 < initialIndexDensity U D) (hb:0≤β) (hbα:β≤α/8)
    (hb1:β≤1/4) (he:0<ε) (hm:0<m)
    (γ δPbal δP:ℝ) (hγ:0≤γ) (hγα:γ≤α/2) (hβbal:β≤δPbal) (hβP:β≤δP)
    (L:ℕ) (hL:L<Q.length):
    ∀i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i
      let I:=markedVortexInnerVertices Q i
      let J:=markedVortexInnerHubs Q i
      let Dbal:=2*(J.card:ℝ)/initialIndexDensity U D
      let Dlevel:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      (∀ x:W,|(((G.comap f).neighborFinset x∩I).card:ℝ)-Dbal|≤δPbal*Fintype.card W) ∧
      (∀ x:W,(1/2+γ)*I.card≤(((G.comap f).neighborFinset x∩I).card:ℝ)) ∧
      (∀ x:W,|((G.comap f).degree x:ℝ)-Dlevel|≤δP*Fintype.card W) ∧
      (∀ x:W,(1/2+γ)*Fintype.card W≤((G.comap f).degree x:ℝ)) ∧
      (Fintype.card W:ℝ)/2≤Dlevel ∧ Dlevel≤2*Fintype.card W := by
  have hInner:=marked_vortex_inner_level_degree_inputs Q hreg hn hD hα hρ hb hbα hb1 he hm
    (γ/2) δPbal (by linarith) hβbal L hL
  have hParent:=marked_vortex_parent_level_degree_inputs Q hreg hn hD hα hρ hb hbα hb1 he hm δP hβP L hL
  intro i hi W Z f I J Dbal Dlevel
  obtain ⟨hRegI,hMinI,hErr⟩:=hInner i hi
  obtain ⟨hMinP,hRegP,hLo,hHi⟩:=hParent i hi
  refine ⟨fun x=>(hRegI x).trans hErr,?_,hRegP,?_,hLo,hHi⟩
  · intro x
    have h:=hMinI x
    convert h using 1 <;> ring
  · intro x
    have hh:=hMinP x
    have hW:0≤(Fintype.card W:ℝ):=Nat.cast_nonneg _
    have hcoef:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)+γ≤1/2+α/2 by linarith) hW
    exact hcoef.trans hh
end Oberwolfach
