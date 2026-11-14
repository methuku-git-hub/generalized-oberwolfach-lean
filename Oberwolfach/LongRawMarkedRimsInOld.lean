module

public import Oberwolfach.LongRawSourceFamilyWheelEdges
public import Oberwolfach.WheelRunPhysicalEdgeSaturation

@[expose] public section
/-! Every selected marked wheel rim edge is in the actual old packing, not
merely in the matching allocation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawMarkedRimsInOldFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_marked_rims_in_old
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X A B:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)] [∀w,DecidableEq (A w)] [∀w,DecidableEq (B w)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (F:∀w,SimpleGraph (X w)) (data:∀w,ActualResidualData (K:=A w) (J:=B w) (F w)) (ψ:∀w,X w→Fin n)
    (Pack:Finset (Sym2 (Fin n))):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let e:=Function.Embedding.subtype (·∈T)
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    (∀w,ActualWheelRimsFamilyOld (data w) (ψ w) _ _ _ _ m (3*d) π _ _ (longRawMarkedWheelsAtHub P π d m ℓ raw g j M w))→
    (∀w,((data w).deletedEdges\(Finset.univ.biUnion (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))⊆Pack)→
    ∀w W,W∈longRawMarkedWheelsAtHub P π d m ℓ raw g j M w→∀a:Sym2 (Fin n),
      a.toFinset∈markedCyclePhysicalEdges _ _ _ _ m π (3*d) W.1→a∈Pack:=by
  intro T e M hW hold w W hmem a ha
  obtain ⟨edge,he,heq⟩:=hW w W hmem a.toFinset ha
  have hh:edge=a:=sym2_toFinset_injective_local heq
  exact hh ▸ hold w he
end Oberwolfach
