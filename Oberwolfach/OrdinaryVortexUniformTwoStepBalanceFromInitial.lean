module

public import Oberwolfach.OrdinaryVortexInitialAmbientBalanceAt
public import Oberwolfach.OrdinaryVortexUniformTwoStepBothBalance

@[expose] public section
/-! The common initial row/index tests and one two-step protected history
supply the current inner and outer-to-inner balances on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_uniform_two_step_balance_from_initial
    (ε ρ₀ α pmin hmin ηInitial cBoundary δInitial:ℝ) (d:ℕ) (β:ℝ) (mInitial:ℕ)
    (hInitialAt:OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial)
    (P JQ G:SimpleGraph V) (JH Hs:V→U→Prop) (D m:ℕ)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1) (hm:mInitial≤m)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (pR pH θ εR εH βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
    (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (hpR:pmin≤pR) (hpR1:pR≤1) (hpH:hmin≤pH) (hθ:1/2≤θ) (hdegree:(θ+α)*Fintype.card V≤D)
    (hεR:0≤εR) (hεRδ:εR≤δInitial) (hεH:0≤εH) (hεHδ:εH≤δInitial)
    (hβe:0≤βe) (hβec:βe≤cBoundary*ε) (hβh:0≤βh) (hβhc:βh≤cBoundary*ε)
    (hpEq:pR=initialIndexDensity U D*pH) (hs:∀u,s u j=pH)
    (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1∧u∈Q.extendedIndices 1))
    (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε Q π hπ pR pH s j σ)
    (r i L:ℕ) (hi:i+1<Q.length) (hiL:i<L) (cost deepCost:ℕ→ℝ)
    (A:Finset (Sym2 V⊕(V×U))) (inner cross:ℕ→ℕ→ℝ):
    let Jraw:=rawWheelSpokes π d σ j;
    let S:=(rawWheelGraph P σ\permutationConflictGraph π (3*d))\JQ;
    let H:=fun v u=>Jraw v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S K;
    let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    OrdinaryUniformProtectedBalanceHistory S₀ H₀
      (fun t=>Q.extendedVertices (t+1)) (fun t=>Q.extendedVertices (t+2))
      (fun t=>Q.extendedIndices (t+1)) (fun t=>Q.extendedIndices (t+2))
      cost deepCost r (i+1) L A (fun t=>Q.extendedVertices (t+2))
      (fun t=>Q.extendedVertices (t+1)) (fun t=>Q.extendedIndices (t+2))
      (fun t=>Finset.Icc (t+3-2) t) inner cross→
    ordinaryHostResources G Hs=A→
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let I:=markedVortexInnerVertices Q (i+1);let J:=markedVortexInnerHubs Q (i+1);
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:J=>Hs (f v.val) (g u.val))).card|≤ηInitial*I.card) ∧
    (∀v,v∉I→|(((G.comap f).neighborFinset v∩I).card:ℝ)-
      2*(J.filter (fun u=>Hs (f v) (g u))).card|≤ηInitial*I.card+2*deepCost i):=by
  intro Jraw S H S₀ H₀ hist hstate f g I J
  have hInitial:=hInitialAt V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi hm Q π hπ
    pR pH θ εR εH βe βh s j σ K hpR hpR1 hpH hθ hdegree hεR hεRδ hεH hεHδ
    hβe hβec hβh hβhc hpEq hs hJQ hJH havoid hgood i hi
  have hinitInner:∀v∈Q.extendedVertices (i+2),
      |((spanningRestriction S₀ (Q.extendedVertices (i+2))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H₀ v u∧v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2))).card|≤ηInitial*I.card:=by
    intro v hv
    convert hInitial.1 v hv using 1 <;> congr! 8 <;> try (apply Finset.ext;intro x;simp [H₀,H,Jraw,and_assoc]) <;> try rfl <;> try (apply congrArg Finset.card;ext u;simp [H₀,H,Jraw,and_assoc])
    funext x y
    simp [H₀,H,Jraw,and_assoc]
  have hinitCross:∀v∈Q.extendedVertices (i+1),v∉Q.extendedVertices (i+2)→
      |((S₀.neighborFinset v∩Q.extendedVertices (i+2)).card:ℝ)-
        2*((Q.extendedIndices (i+2)).filter (H₀ v)).card|≤ηInitial*I.card:=by
    intro v hv hv'
    convert hInitial.2 v hv hv' using 1 <;> congr! 8 <;> try (apply Finset.ext;intro x;simp [H₀,H,Jraw,and_assoc]) <;> try rfl <;> try (apply congrArg Finset.card;ext u;simp [H₀,H,Jraw,and_assoc])
    funext y
    simp [H₀,H,Jraw,and_assoc]
  have hboth:=ordinary_vortex_uniform_two_step_both_balance P S₀ G H₀ Hs D m β ε Q r i L hiL cost deepCost A inner cross
    (ηInitial*I.card) hist hstate
    (by intro v hv;convert hinitInner v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv hv';convert hinitCross v hv hv' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  constructor
  · intro v;convert hboth.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv;convert hboth.2 v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
