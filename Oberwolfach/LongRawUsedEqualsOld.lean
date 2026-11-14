module

public import Oberwolfach.LongRawCandidateRimClassification
public import Oberwolfach.WheelRunPhysicalEdgeSaturation

@[expose] public section
/-! Once both types of selected wheel rim are embedded, the matching allocation
is exactly the actual old edge packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawUsedEqualsOldFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_used_equals_old
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (Pack:Finset (Sym2 (Fin n))):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let e:=Function.Embedding.subtype (·∈T)
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet (mixedCandidateResources R) e) M;
    Pack⊆Used.edgeFinset→
    (∀a:LongRawSelectedMarked π d m ℓ e M,∀edge:Sym2 (Fin n),
      edge.toFinset∈markedCyclePhysicalEdges _ _ _ _ m π (3*d) (longRawSelectedMarkedWheel P π d m ℓ raw g j M a).1→edge∈Pack)→
    (∀a:LongRawSelectedOrdinary π d m ℓ e M,∀k,
      s((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val k,
        (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val (cycleNext k))∈Pack)→
    Pack=Used.edgeFinset:=by
  intro T e R φ M Used hPack hMarked hOrd
  apply Finset.Subset.antisymm hPack
  intro edge he
  induction edge using Sym2.ind with
  | _ x y =>
    have hxy:Used.Adj x y:=SimpleGraph.mem_edgeFinset.mp he
    have hh:=long_raw_candidate_rim_classification P π d m ℓ raw g j M x y hxy
    have hdec:longRawCandidateRimClassFin n=longRawUsedEqualsOldFin n:=Subsingleton.elim _ _
    have hdecK:longRawCandidateRimClassFin K=longRawUsedEqualsOldFin K:=Subsingleton.elim _ _
    try rw [hdec,hdecK] at hh
    rcases hh with ⟨a,ha⟩|⟨a,k,ha⟩
    · exact hMarked a s(x,y) ha
    · have heq:s(x,y)=s((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val k,
          (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val (cycleNext k)):=by
        apply sym2_toFinset_injective_local
        simpa only [Sym2.toFinset_mk_eq] using ha
      rw [heq]
      exact hOrd a k
end Oberwolfach
