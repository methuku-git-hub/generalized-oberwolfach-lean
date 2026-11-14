module

public import Oberwolfach.MarkedVortexAssembledSizeFields
public import Oberwolfach.MarkedVortexAssembledDegreeFields
public import Oberwolfach.MarkedVortexLevelMinimumSizes
public import Oberwolfach.MarkedVortexActiveDegreeRecordInputs

@[expose] public section
/-! A single terminal-scale choice gives the actual size and degree fields at
all levels, with the scale chosen before the host and vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_uniform_geometric_record_fields
    (α ρ₀ ε κ hcut ξ xiDeep ω x:ℝ) (N NI:ℕ)
    (hN:1≤N) (hα:0<α) (hρ₀:0<ρ₀) (he:0<ε) (he8:ε≤1/8) (heAlpha:ε≤α/8)
    (heκ:ε≤κ) (hecut:ε≤hcut) (heξ:4*ε≤ξ) (hedeep:ε^2≤xiDeep)
    (hω:0≤ω) (hωv:ω≤ε/8) (hωu:ω≤ρ₀*ε/64):
    ∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
      G.IsRegularOfDegree D → 0<Fintype.card V →
      (1/2+α)*Fintype.card V≤(D:ℝ) →
      ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D≤1 →
      0≤β → β≤1/4 → β≤α/8 → β≤3*α/40 → β≤3/20 → β≤κ → β≤x → m₀≤m →
      ∀ L:ℕ,L<Q.length →
      let gamma:=α/16
      let alphaInner:=α/8
      let iota:=ε/4
      let omegaI:=ρ₀/16
      let omegaParent:=ρ₀/8;
    (∀ i≤L,
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
      omegaI*I.card≤(J.card:ℝ) ∧ J.card≤I.card) ∧
    (∀ i≤L,
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
      0≤errParent ∧ errParent≤x*Fintype.card W) ∧
    (∀ i≤L,
      let VP:=markedVortexVertexType Q i
      let I:=markedVortexInnerVertices Q i
      let W:=↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
        Finset (markedVortexVertexType Q (i+1)));
      N≤Fintype.card VP ∧ N≤Fintype.card W ∧ NI≤I.card) ∧
    (∀ i≤L,
      let W:=↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
        Finset (markedVortexVertexType Q (i+1)))
      let Zinner:=markedVortexInnerNonDeeperHubs Q i
      let Dactive:=2*(Zinner.card:ℝ)/initialIndexDensity U D;
      (Fintype.card W:ℝ)/2≤Dactive ∧ Dactive≤2*Fintype.card W) := by
  have hequarter:ε≤1/4 := by linarith
  obtain ⟨m₀,hm₀,hmin⟩:=marked_vortex_level_minimum_sizes ρ₀ ε hρ₀ he hequarter N NI
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hD hρlo hρhi hb hb1 hbα hbαstrong hbstrong hbκ hbx hm L hL gamma alphaInner iota omegaI omegaParent
  have hDhalf:(Fintype.card V:ℝ)/2≤D := by
    have hn0:(0:ℝ)≤Fintype.card V := Nat.cast_nonneg _
    nlinarith
  have hmpos:0<m := by omega
  have hρ:0 < initialIndexDensity U D := lt_of_lt_of_le hρ₀ hρlo
  obtain ⟨_,_,_,_,_,_,hsize⟩:=marked_vortex_assembled_size_fields Q hreg hn hDhalf hρ₀ hρlo hρhi hb hb1 he he8 hmpos
    κ hcut ξ xiDeep ω alphaInner (by dsimp [alphaInner];exact heAlpha) heκ hecut heξ hedeep hω hωv hωu L hL
  have hdeg:=marked_vortex_assembled_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he hmpos κ x hbκ hbx L hL
  have hmin' := hmin V U G D m β Q hreg hn hDhalf hρlo hρhi hb hb1 hm L hL
  have hW:∀ i≤L,0<Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
      Finset (markedVortexVertexType Q (i+1))) := by
    intro i hi
    have hh: N≤Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
        Finset (markedVortexVertexType Q (i+1))) := (hmin' i hi).2.1
    omega
  have hactive:=marked_vortex_active_degree_record_inputs Q hreg hn hD hα hρ hb hbαstrong hbstrong he.le hequarter L hW
  exact ⟨hsize,hdeg,hmin',hactive⟩
end Oberwolfach
