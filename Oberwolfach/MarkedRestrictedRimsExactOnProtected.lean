module

public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section
/-! Exact preservation on a protected vertex set makes the restricted rim
relation identical, even if the hub restriction is much larger. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_restricted_rims_exact_on_protected
    {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]
    (f:W→V) (g:Z→U) (I:Finset V) (hf:∀x,f x∈I)
    (σ τ:RawMarkedOutcome V U Γ Color)
    (hprotected:∀e:Sym2 V,e.toFinset⊆I→τ (Sum.inl e)=σ (Sum.inl e))
    (P:SimpleGraph W) (ρ:Equiv.Perm W) (d:ℕ):
    rawMarkedPairRims P ρ d (rawMarkedRestrictPair f g τ)=
      rawMarkedPairRims P ρ d (rawMarkedRestrictPair f g σ) :=by
  have hlabels:(fun e=>rawMarkedRestrictPair f g τ (Sum.inl e))=
      (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)):=by
    funext e
    change τ (Sum.inl (Sym2.map f e))=σ (Sum.inl (Sym2.map f e))
    apply hprotected
    induction e using Sym2.ind with
    | _ x y =>
      change s(f x,f y).toFinset⊆I
      intro v hv
      simp only [Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact hf x
      · exact hf y
  funext e
  cases e <;> simp only [rawMarkedPairRims,Sum.elim_inl,Sum.elim_inr,hlabels]
end Oberwolfach
