module

public import Oberwolfach.OrdinaryInitialFineCoverFromSharedNumeric

@[expose] public section
/-! A fixed size threshold for the initial fine-cover callback on any
balanced edited host with the shared sampled tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryInitialFineCoverFromSharedAt
    (mWheel loadK d:ℕ)
    (ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut pstar β:ℝ)
    (v₀:ℕ):Prop :=
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P G:SimpleGraph V) (Hs:V→U→Prop) (D mv:ℕ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤mv→
    ∀(Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (j:Color) (sp:U→Color→ℝ)
      (pR pH density εR εH Ledit βe βh:ℝ),
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let I:=markedVortexInnerVertices Q 0;let T:=ordinaryVortexBufferedVertices Q 0 2;
    let B:=markedVortexInnerHubs Q 0;let W:=ordinaryVortexBufferedHubs Q 0 2;
    let ρi:=markedVortexPermutation Q π hπ 0;
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);
    let raw:=ordinaryRawRestrictPair f g σ;
    pmin≤pH→pH≤1→0<pH→0≤εR→εR≤εsample→0≤εH→εH≤εsample→0≤Ledit→Ledit≤ζlimit*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density
      (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>sp (g u)) j raw→
    (∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤ηbal*I.card)→
    G≤P→(∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryFixedVortexDeepCoverEvent mWheel loadK d a aLoad ρ θ P D mv β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices 1) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    OrdinaryFineWheelCoverResult mWheel loadK ξroot aLoad Gloc Floc Hloc I T B W
end Oberwolfach
