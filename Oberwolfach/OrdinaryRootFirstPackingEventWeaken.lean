module

public import Oberwolfach.OrdinaryRootFirstPackingWeaken
public import Oberwolfach.TwoStageEvents

@[expose] public section
/-! Enlarge the threshold on a packing event without changing its selected
cover or reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_packing_event_weaken
    {V U Ω:Type} [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U]
    (μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ)
    (Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (X T:Ω→Finset V) (Z W:Ω→Finset U)
    (r:ℕ) (η ell:ℝ) (t t':Ω→ℝ)
    (D:∀s,OrdinaryRootCoverData (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r η ell)
    (R:Ω→SimpleGraph (V⊕U)) (hbound:∀s,E s→t s≤t' s)
    (hp:1-e≤μ.probability (fun s=>E s ∧
      ∃K:OrdinaryRootFirstPackingContext (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r η ell (t s),
        K.cover=D s ∧ K.reserve=R s)):
    1-e≤μ.probability (fun s=>E s ∧
      ∃K:OrdinaryRootFirstPackingContext (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r η ell (t' s),
        K.cover=D s ∧ K.reserve=R s):=by
  apply hp.trans
  apply finiteLaw_probability_mono
  intro s hs
  obtain ⟨hsE,K,hD,hR⟩:=hs
  obtain ⟨K',hD',hR'⟩:=ordinary_root_first_packing_weaken (Q s) (F s) (H s) (X s) (T s) (Z s) (W s)
    r η ell (t s) (t' s) K (hbound s hsE)
  exact ⟨hsE,K',hD'.trans hD,hR'.trans hR⟩
end Oberwolfach
