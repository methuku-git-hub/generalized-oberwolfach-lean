module

public import Oberwolfach.LongMatchingWitnessCorrection
public import Oberwolfach.LongSelectedTypedRawDirection
public import Oberwolfach.LongSelectedMarkedOrientationPreserved

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_matching_witness_preserves_inner_marked_direction
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z T K θ D alpha γ eps βList F hF weight w D₀ C S M Del):
    ∀x∈T,∀y∈T,markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)=1→M x y=1:=by
  intro x hx y hy hMark
  have hraw:=long_selected_marked_raw_direction G π d (fun e=>z.1 (Sum.inl e)) x y hMark
  have hG:G.Adj x y:=by by_contra h;simp [sampledColourOrientation,h] at hraw
  have hxy:x≠y:=hG.ne
  have hZ:(spanningRestriction (⊤:SimpleGraph (Fin n)) T).Adj x y:=by
    simp only [spanningRestriction_adj,SimpleGraph.top_adj]
    exact ⟨hxy,hx,hy⟩
  have hDel:¬Del.Adj x y:=by
    intro h
    have hp:=hw.2.2.2.2.2.2.1 x y h
    exact hp (Or.inl hZ)
  have hc:=long_matching_witness_correction_bound Δ G π z T θ D alpha γ eps βList F hF weight w D₀ C S Del M hw
  exact long_selected_marked_direction_preserved G Del z.1 M hc.1 x y hraw.1 hDel
end Oberwolfach
