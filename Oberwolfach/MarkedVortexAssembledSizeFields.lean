module

public import Oberwolfach.MarkedVortexActiveDensityInputs
public import Oberwolfach.MarkedVortexActiveInnerSizeInput
public import Oberwolfach.MarkedVortexInnerActiveSizeInputs
public import Oberwolfach.MarkedVortexInnerHubSizes
public import Oberwolfach.MarkedFixedVortexParentHubDensity
public import Oberwolfach.MarkedVortexTwoStepRemainderInputs

@[expose] public section
/-! Assemble the actual vortex size estimates using the early geometric
choices; the same lower bounds work at every selected level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_assembled_size_fields
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ:0<ρ₀)
    (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (he8:ε≤1/8) (hm:0<m)
    (κ hcut ξ xiDeep ω alphaInner:ℝ) (heAlpha:ε≤alphaInner) (heκ:ε≤κ) (hecut:ε≤hcut) (heξ:4*ε≤ξ)
    (hedeep:ε^2≤xiDeep) (hω:0≤ω) (hωv:ω≤ε/8) (hωu:ω≤ρ₀*ε/64)
    (L:ℕ) (hL:L<Q.length):
    let iota:=ε/4
    let omegaI:=ρ₀/16
    let omegaParent:=ρ₀/8;
    0 < iota ∧ iota≤ε/2 ∧ 0<omegaI ∧ omegaI≤ρ₀/8 ∧
    0<omegaParent ∧ omegaParent≤1 ∧
    ∀ i≤L,
      let VP:=markedVortexVertexType Q i
      let UP:=markedVortexHubType Q i
      let I:=markedVortexInnerVertices Q i
      let J:=markedVortexInnerHubs Q i
      let T:=markedVortexDeeperVertices Q i
      let R:=markedVortexDeeperHubs Q i
      let Vkeep:=markedVortexNonDeeperVertexType Q i
      let Ukeep:=markedVortexNonDeeperHubType Q i
      let W:=↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
        Finset (markedVortexVertexType Q (i+1)))
      let X:=Finset.univ.image (markedVortexNextActiveInNonDeeper Q i)
      let Z:=markedVortexInnerNonDeeperHubs Q i;
      Fintype.card UP≤Fintype.card VP ∧
      omegaParent*Fintype.card VP≤(Fintype.card UP:ℝ) ∧
      (I.card:ℝ)≤ξ*Fintype.card VP ∧ (J.card:ℝ)≤ξ*Fintype.card VP ∧
      (T.card:ℝ)≤κ*Fintype.card VP ∧ (R.card:ℝ)≤κ*Fintype.card VP ∧
      (T.card:ℝ)≤hcut*I.card ∧ (R.card:ℝ)≤hcut*J.card ∧
      (T.card:ℝ)≤alphaInner*I.card ∧
      (T.card:ℝ)≤xiDeep*Fintype.card VP ∧ (R.card:ℝ)≤xiDeep*Fintype.card VP ∧
      (Fintype.card VP:ℝ)/2≤Fintype.card Vkeep ∧
      ω*Fintype.card (Vkeep⊕Ukeep)≤(Fintype.card W:ℝ) ∧
      ω*Fintype.card (Vkeep⊕Ukeep)≤(Z.card:ℝ) ∧
      ((ordinaryInnerVertices X Z).card:ℝ)≤ξ*Fintype.card Vkeep ∧
      iota*Fintype.card VP≤(I.card:ℝ) ∧ iota*Fintype.card VP/4≤(Fintype.card W:ℝ) ∧
      omegaI*I.card≤(J.card:ℝ) ∧ J.card≤I.card := by
  have hDpos:0<D := by
    have hn' : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
    exact_mod_cast (show (0:ℝ)<D by linarith)
  have hehalf:ε≤1/2 := by linarith
  have heκ2:ε^2≤κ := by nlinarith [sq_nonneg (1-ε)]
  have heξ':ε≤ξ := by linarith
  intro iota omegaI omegaParent
  have hi:0 < iota := by dsimp [iota]; positivity
  have hiCap:iota≤ε/2 := by dsimp [iota]; linarith
  have ho:0<omegaI := by dsimp [omegaI]; positivity
  have hoCap:omegaI≤ρ₀/8 := by dsimp [omegaI]; linarith
  have hparent:0<omegaParent := by dsimp [omegaParent]; positivity
  have hparent1:omegaParent≤1 := by
    have hh:ρ₀≤1 := hρlo.trans hρhi
    dsimp [omegaParent]; linarith
  refine ⟨hi,hiCap,ho,hoCap,hparent,hparent1,?_⟩
  intro i hiL VP UP I J T R Vkeep Ukeep W X Z
  have hambient:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ hρlo hρhi hb hb1 he hm i (by omega)
  have hparentDensity:=marked_vortex_fixed_parent_hub_density Q hreg hn hD hρ hρlo hb hb1 i (by omega)
  have hu:=marked_vortex_inner_upper_size_inputs Q hreg hn hDpos hρhi he.le ξ heξ' L hL i hiL
  have hd:=marked_vortex_two_step_remainder_inputs Q hreg hn hDpos hρhi he.le hehalf κ hcut xiDeep heκ2 hecut hedeep L hL i hiL
  have hgeom:=marked_vortex_fixed_active_geometry Q he.le i
  have hTalpha:(T.card:ℝ)≤alphaInner*I.card :=
    hgeom.2.2.1.trans (mul_le_mul_of_nonneg_right heAlpha (Nat.cast_nonneg _))
  have ha:=marked_vortex_active_density_inputs Q hreg hn hD hρ hρlo hρhi hb hb1 he hehalf hm ω hω hωv hωu L hL i hiL
  have hsmall:=marked_vortex_active_inner_size_input Q hreg hn hDpos hρhi he.le hehalf ξ heξ L hL i hiL
  have hlo:=marked_vortex_inner_active_size_inputs Q he hehalf hm iota hi.le hiCap L hL i hiL
  have hhub:=marked_vortex_inner_hub_sizes Q hreg hn hD hρ hρlo hρhi hb hb1 he hm omegaI hoCap L hL i hiL
  exact ⟨hambient.2.2,hparentDensity,hu.1,hu.2,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hTalpha,hd.2.2.2.2.1,hd.2.2.2.2.2.1,hd.2.2.2.2.2.2,ha.1,ha.2,hsmall,hlo.1,hlo.2,hhub.1,hhub.2⟩
end Oberwolfach
