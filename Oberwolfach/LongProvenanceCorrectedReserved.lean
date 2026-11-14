module

public import Oberwolfach.LongFactorComplementCorrectedSpokeGeometry
public import Oberwolfach.MarkedRobustChangedSampleReserved
public import Oberwolfach.MarkedExpandedActualSample

@[expose] public section
/-! The actual factor-complement provenance supplies type separation for the
same corrected encoding, so the selected robust event gives its terminal absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance provenanceCorrectedReservedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_provenance_corrected_reserved
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (F:U→SimpleGraph (Fin n)) (S P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ) (hd:1≤d)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (ε ζ cap:ℝ) (size a₀ b₀ e₀ f:ℕ) (hζ:0≤ζ)
    (hstable:MarkedRetainedRobustChangeEvent P π d r false false ε ζ cap size a₀ b₀ e₀ f (markedExpandedActualSelected π d z))
    (Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n))) (A:Finset (Fin n×Fin n)) (Spokes:U→Finset (Fin n))
    (τ:RawMarkedOutcome (Fin n) U Bool Bool) (FR:SimpleGraph (Fin n)) (FS:SimpleGraph (Fin n⊕U)):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let old:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)
    let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t z.2 u=>d) Subtype.val
    let H:Bool→Fin n→U→Prop:=fun b v u=>if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false true true v u else v∈Spokes u\Y u;
    LongFactorComplementProvenance F S P π d (r+4) raw t z.2 Pack Enew A Spokes→
    (∀a,¬(rawMarkedPairRims P π d old a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)→
    (∀b v u,¬(retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false false b v u↔H b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀v,(FR.degree v:ℝ)≤cap*n)→(∀v,(FS.degree v:ℝ)≤cap*n)→
    (∀v u,¬(H false v u∧H true v u)) ∧
    (∀u v w,H false v u→H true w u→v≠π w) ∧
    MarkedReservedTerminalAbsorberProperty
      (fun e:MarkedSampleArc P π (3*d) (fun a=>τ (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun a=>τ (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2)
      (H false) (H true) π (3*d) r size a₀ b₀ e₀ f ε :=by
  intro raw old t Y H hprov hR hS hFR hFS
  have hgeometry:=long_factor_complement_corrected_spoke_geometry F S P π d (r+4) hd raw t z.2 Pack Enew A Spokes hprov
  have hAbs:=marked_robust_changed_sample_reserved P π d r false false ε ζ cap size a₀ b₀ e₀ f hζ (markedExpandedActualSelected π d z) hstable τ H FR FS
  have hR':∀a,¬(rawMarkedPairRims P π d (markedExpandedActualSelected π d z).1 a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset:=by
    simpa only [markedExpandedActualSelected,old] using hR
  have hS':∀b v u,¬(retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inr e)) false))
      (markedExpandedActualSelected π d z).2 false false b v u↔H b v u)→FS.Adj (Sum.inl v) (Sum.inr u):=by
    simpa only [markedExpandedActualSelected,raw,t,rawExpandedApproximateCollapse,rawExpandedMarkedCollapse,id] using hS
  refine ⟨hgeometry.1,hgeometry.2,?_⟩
  exact hAbs hR' hS' (by simpa only [Fintype.card_fin] using hFR) (by simpa only [Fintype.card_fin] using hFS) hgeometry.1
end Oberwolfach
