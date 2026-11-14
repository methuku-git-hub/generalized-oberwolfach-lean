module

public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section

/-! The actual fixed coefficients on a smaller vertex domain retain their
omitted-root spoke load bounds after global physical deletions. Restriction
is deterministic and the normalization remains the supplied local one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_domain_spoke_loads_after_global_physical_deletion
    (f:W↪oV) (g:Z↪U) (P:SimpleGraph V) (ρ:Equiv.Perm W) (d m:ℕ)
    (hm:3≤m) (hn:0<Fintype.card W) (D τ aLo B:ℝ)
    (hDlo:(Fintype.card W:ℝ)/2≤D) (hDhi:D≤2*Fintype.card W)
    (p k s₀ pstar:ℝ) (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hB:0≤B)
    (weight:(Fin (m+1)→W)→ℝ)
    (hw:SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τ aLo B weight)
    (eps deltaR deltaS:ℝ) (hR:0≤deltaR) (hS:0≤deltaS)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hload:MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d m D p k s₀ weight eps
      (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z)))
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x:W,((DR.neighborFinset (f x)∩Finset.univ.image f).card:ℝ)≤deltaR)
    (hspoke:∀ z:W⊕Z,((DS.neighborFinset (Sum.map f g z)∩Finset.univ.image (Sum.map f g)).card:ℝ)≤deltaS):
    MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d m D p k s₀ weight
      (eps+5*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*(2*deltaR+deltaS)/Fintype.card W)
      (rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset))
      (fun b x z=>markedDeletePhysicalSpokes H DS b (f x) (g z)):=by
  rw [rawMarkedRestrictPair_deleteRims,markedDeletePhysicalSpokes_restrict]
  apply marked_local_spoke_loads_after_physical_deletion (P.comap f) ρ d m hm hn
    D τ aLo B hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw
    eps deltaR deltaS hR hS (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z)) hload
    (DR.comap f) (DS.comap (Sum.map f g))
  · intro x
    have he:=graph_comap_degree_into_image DR f.toEmbedding x
    exact (congrArg (fun n:ℕ=>(n:ℝ)) he).trans_le (hrim x)
  · intro x
    have he:Function.Injective (Sum.map f g):=Sum.map_injective.mpr ⟨f.injective,g.injective⟩
    have hh:=graph_comap_degree_into_image DS ⟨Sum.map f g,he⟩ (Sum.inl x)
    exact (congrArg (fun n:ℕ=>(n:ℝ)) hh).trans_le (hspoke (Sum.inl x))
  · intro z
    have he:Function.Injective (Sum.map f g):=Sum.map_injective.mpr ⟨f.injective,g.injective⟩
    have hh:=graph_comap_degree_into_image DS ⟨Sum.map f g,he⟩ (Sum.inr z)
    exact (congrArg (fun n:ℕ=>(n:ℝ)) hh).trans_le (hspoke (Sum.inr z))

end Oberwolfach
