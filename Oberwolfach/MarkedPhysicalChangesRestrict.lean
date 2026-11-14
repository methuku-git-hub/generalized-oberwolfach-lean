module

public import Oberwolfach.RawMarkedPairRestriction
public import Oberwolfach.MarkedRimFullIncidence

@[expose] public section
/-! Physical change graphs restrict to the actual active domains, with
marked physical heads transported by the commuting permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z Γ Color:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_physical_changes_restrict
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hcomm:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hR:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)):
    (∀ a,¬(rawMarkedPairRims (P.comap f) ρ d (rawMarkedRestrictPair f g σ) a↔
      rawMarkedPairRims (P.comap f) ρ d (rawMarkedRestrictPair f g τ) a)→
      markedPairPhysical ρ a∈(FR.comap f).edgeFinset) ∧
    (∀ b v u,¬(H b (f v) (g u)↔H' b (f v) (g u))→
      (FS.comap (Sum.map f g)).Adj (Sum.inl v) (Sum.inr u)) := by
  constructor
  · intro a ha
    have hσ:=rawMarkedRestrictPair_rims f g π ρ hcomm P d σ a
    have hτ:=rawMarkedRestrictPair_rims f g π ρ hcomm P d τ a
    have hb:¬(rawMarkedPairRims P π d σ (Sum.map (Prod.map f f) (Prod.map f f) a)↔
      rawMarkedPairRims P π d τ (Sum.map (Prod.map f f) (Prod.map f f) a)):=by tauto
    have hc:=hR _ hb
    cases a with
    | inl a=>
      rcases a with ⟨x,y⟩
      simpa only [markedPairPhysical,Sum.elim_inl,Sum.map_inl,Prod.map,SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet,SimpleGraph.comap_adj] using hc
    | inr a=>
      rcases a with ⟨x,y⟩
      simpa only [markedPairPhysical,Sum.elim_inr,Sum.map_inr,Prod.map,SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet,SimpleGraph.comap_adj,hcomm] using hc
  · intro b v u h
    exact hS b (f v) (g u) h
end Oberwolfach
