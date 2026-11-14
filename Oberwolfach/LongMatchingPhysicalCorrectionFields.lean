module

public import Oberwolfach.LongEveryClassSameDeletionReady

@[expose] public section
/-! Project the host orientation, correction and deletion bounds from the
same class-matching witness used for the completed factor packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchingPhysicalCorrectionFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) matchingPhysicalCorrectionSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem long_matching_physical_correction_fields
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (K:ℕ) (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (S Del:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ P π d r z T K θ D alpha γ eps βList F hF weight w D₀ C S M Del):
    (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
    (∀x y,M x y=1→P.Adj x y) ∧
    orientationDisagreementGraph (longPhysicalStateGraph P z.1 {0,1,2,3,4})
      (fun e=>(z.1 (Sum.inl e)).2) M≤Del ∧
    (∀v,(Del.degree v:ℝ)≤Δ*n):=by
  rcases hw with ⟨hphysical,hdegree,hD,hdelete,hcorrect,hDel,havoid,hselected,hK,hhost,hMixed,hLists⟩
  have hstd:everyClassReadyFin 6=instDecidableEqFin 6:=Subsingleton.elim _ _
  rw [hstd] at hcorrect
  exact ⟨hphysical,hhost,hcorrect,hDel⟩
end Oberwolfach
