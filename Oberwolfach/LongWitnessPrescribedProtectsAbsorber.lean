module

public import Oberwolfach.LongWitnessRequiredProtectsFixedAbsorber
public import Oberwolfach.PrescribedFamilyProtectsReservedGraph

@[expose] public section
/-! With free arcs chosen outside the absorber, the prescribed embedding for
the same class witness avoids the fixed absorber in its physical rim graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance witnessPrescribedProtectsAbsorberFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_witness_prescribed_protects_fixed_absorber
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del Used:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S M Del)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) t)
    (X:Finset (Fin n)) (Z:Finset U) (Pack:Finset (Sym2 (Fin n)))
    {Y:U→Type} [∀i,Fintype (Y i)] [∀i,DecidableEq (Y i)]
    (pieces:∀i,List (PrescribedSourcePiece (Y i))) (Φ:∀i,Y i→Fin n) (Dfree:Fin n→Fin n→Prop):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false t J false false
    MarkedFixedTerminalAbsorber G π d (r+4) raw H C X Z→
    Disjoint (longSelectedPhysicalGraph G π d z.1) Used→
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let RMark:=fun x y=>markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)=1
    let Req:=fun x y=>M x y=1 ∧ ¬RMark x y
    let Kbad:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Old:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))
    let Kplus:=Kbad⊔spanningRestriction (Used\Old) I
    (∀i x y,prescribedDependentDigraph pieces i x y→
      (Dfree (Φ i x) (Φ i y) ∧ ¬(markedResourceRimGraph C).Adj (Φ i x) (Φ i y)) ∨ Kplus.Adj (Φ i x) (Φ i y))→
    let E:=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
    ∀x y,(prescribedPhysicalUnion E).Adj x y→¬(markedResourceRimGraph C).Adj x y:=by
  intro raw H habs hdis Sel RMark Req Kbad Old Kplus harc E
  have hK:=long_matching_witness_required_protects_fixed_absorber Δ G π z I θ D alpha γ eps βList F hF weight w D₀ C S Del Used M hw t J X Z Pack habs hdis
  apply prescribed_family_protects_reserved_graph pieces Φ Dfree Kplus (markedResourceRimGraph C) ?_ harc
  intro x y hk hr
  exact hK x y hr hk
end Oberwolfach
