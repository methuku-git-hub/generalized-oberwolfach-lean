module

public import Oberwolfach.OrdinaryVortexInitialProtectedAmbientBalance
public import Oberwolfach.OrdinaryVortexInitialSeparatedMarginsBeforeSpacing

@[expose] public section
/-! Uniform initial ambient balance on the protected corrected sample. The
constants are selected before the finite host and before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_initial_ambient_balance_uniform_before_spacing
    (ρ₀ α pmin hmin:ℝ) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃cBoundary:ℝ,0<cBoundary ∧ ∀ε:ℝ,0<ε→ε<1/4→∀η:ℝ,0<η→
    ∃δ:ℝ,0<δ ∧ δ≤α ∧ δ≤η ∧ ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δ→
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U] (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (pR pH θ εR εH βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
      (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U))),
      pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)→
      (∀v u,JH v u→¬(v∈Q.extendedVertices 1∧u∈Q.extendedIndices 1))→
      Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε Q π hπ pR pH s j σ→
    let S:=(rawWheelGraph P σ\permutationConflictGraph π (3*d))\JQ;
    let S₀:=S\ordinaryResourceRim S K;
    let H₀:=fun v u=>rawWheelSpokes π d σ j v u∧¬JH v u∧¬(Sum.inr (v,u)∈K);
    ∀i:ℕ,i+1<Q.length→
    let I:=markedVortexInnerVertices Q (i+1);
    (∀v∈Q.extendedVertices (i+2),|((spanningRestriction S₀ (Q.extendedVertices (i+2))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H₀ v u∧v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2))).card|≤η*I.card) ∧
    (∀v∈Q.extendedVertices (i+1),v∉Q.extendedVertices (i+2)→
      |((S₀.neighborFinset v∩Q.extendedVertices (i+2)).card:ℝ)-
        2*((Q.extendedIndices (i+2)).filter (H₀ v)).card|≤η*I.card) :=by
  obtain ⟨c,hc,hmain⟩:=ordinary_vortex_initial_separated_margins_before_spacing ρ₀ α pmin hmin hρ₀ hα hpmin hhmin
  refine ⟨c,hc,?_⟩
  intro ε hε hε1 η hη
  obtain ⟨δ,hδ,hδα,hδη,hδmain⟩:=hmain ε hε hε1 η hη
  refine ⟨δ,hδ,hδα,hδη,?_⟩
  intro d β hβ hβ1 hβδ
  obtain ⟨m₀,hm₀,hm⟩:=hδmain d β hβ hβ1 hβδ
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m hreg hn hD hρlo hρhi hmm Q π hπ
    pR pH θ εR εH βe βh s j σ K hpR hpR1 hpH hθ hdegree hεR hεRδ hεH hεHδ
    hβe hβec hβh hβhc hpEq hs hJQ hJH havoid hgood S S₀ H₀ i hi I
  have hρ:0< initialIndexDensity U D:=lt_of_lt_of_le hρ₀ hρlo
  have hPR:0≤pR:=le_trans hpmin.le hpR
  have hPH:0≤pH:=le_trans hhmin.le hpH
  have hβα:β≤2*α:=by linarith
  have hmarg:=hm V U P D m hreg hn hD hρlo hρhi hmm Q (i+1) hi pR pH θ εR εH βe βh
    hpR hpR1 hpH hθ hεR hεRδ hεH hεHδ hβe hβec hβh hβhc hpEq
  have hh:=ordinary_vortex_initial_protected_ambient_balance P JQ JH D m β ε θ α pR pH εR εH βe βh η
    Q π hπ d s j σ hn hreg hρ hβ hPR hpR1 hPH hεR hεH hθ hβα hdegree hpEq hs K hJQ hJH havoid hgood i hi
    hmarg.1 hmarg.2.1 hmarg.2.2
  have ht:=And.intro hh.2.2.2.1 hh.2.2.2.2
  convert ht using 1 <;> congr! 8 <;> try (apply Finset.ext; intro x; simp [H₀, and_assoc, Nat.add_assoc]) <;> try rfl <;> try (apply congrArg Finset.card; ext u; simp [H₀, and_assoc, Nat.add_assoc]) <;> try simp [H₀, and_assoc, Nat.add_assoc] <;> try omega
  have hi2 : i+2=i+1+1 := by omega
  rw [hi2]
  congr 1
  ext u
  simp [H₀, and_assoc]
end Oberwolfach
