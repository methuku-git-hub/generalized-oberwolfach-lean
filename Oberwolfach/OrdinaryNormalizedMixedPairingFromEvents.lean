module

public import Oberwolfach.OrdinaryNormalizedHubFactorTwoAvoidance
public import Oberwolfach.OrdinaryFreshPhysicalEndpointEvent
public import Oberwolfach.MixedFreshPairingParentInsideRoots
public import Oberwolfach.LocalFactorGraphChoice
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
/-! Select disjoint hub factors and endpoint pairings from events on the
same physical sample, allowing their tolerances to have separate origins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U K:Type} [Fintype V] [Fintype U] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq K]

theorem ordinary_normalized_mixed_pairing_from_events
    (m:ℕ) (ρ:ℝ) (hρ:0<ρ):∃N:ℕ,
    ∀(V U K:Type) [Fintype V] [Fintype U] [Fintype K] [DecidableEq V] [DecidableEq U] [DecidableEq K],
    N≤Fintype.card (V⊕U)→∀(Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
      (P B:SimpleGraph (V⊕U)) (S R:K→Finset (V⊕U)) (g:K→(V⊕U)↪Sym2 (V⊕U))
      (p ζ ζh ζe:ℝ) (hp:0≤p) (hζh:ζ≤ζh) (hζe:ζ≤ζe)
      (hmap:(spanningRestriction Q A).map (Function.Embedding.inl:V↪V⊕U)≤P)
      (σ:Sym2 (V⊕U)→Bool),
    OrdinaryNormalizedHubFactorEvent m Q F H A Z p ζh σ→
    OrdinaryFreshPhysicalEndpointEvent P B S R g p ζe σ→
    MixedFreshPairingAvoidingEvent m p ρ ζ (spanningRestriction Q A) F P B
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z A) S R
      (fun j=>hubSpokeCoin j.val) g σ:=by
  obtain ⟨N,hN⟩:=select_mixed_boundary_pairings_avoiding ρ hρ
  refine ⟨N,?_⟩
  intro V U K _ _ _ _ _ _ hn Q F H A Z P B S R g p ζ ζh ζe hp hζh hζe hmap σ hhub hend
  let T:=ordinaryBoundaryHubSet H Z A
  let e:V↪V⊕U:=Function.Embedding.inl
  intro Zdel ℓ hZ Y S' R' hYT hdiv hS hR hratio hchangeY hchangeS hchangeR hinter hmem hbudgetY hbudgetE
  apply hN V (V⊕U) {u:U // u∉Z} K hn (m+1) (spanningRestriction Q A) F P B Zdel e hmap
    T Y S' R' hinter hmem
  · intro j C hC
    have hscale:ζ*(p*(T j).card)≤ζh*(p*(T j).card):=
      mul_le_mul_of_nonneg_right hζh (by positivity)
    have hd (v:V):((C⊔Zdel.comap e).degree v:ℝ)≤ζh*(p*(T j).card):=by
      have hsum:((C⊔Zdel.comap e).degree v:ℝ)≤(C.degree v:ℝ)+(Zdel.comap e).degree v:=by
        exact_mod_cast graph_degree_sup_le C (Zdel.comap e) v
      have hzc:((Zdel.comap e).degree v:ℝ)≤ℓ:=
        (Nat.cast_le.mpr (graph_comap_degree_le Zdel e v)).trans (hZ (e v))
      exact hsum.trans ((add_le_add (hC v) hzc).trans ((hbudgetY j).trans hscale))
    exact ordinary_normalized_hub_factor_two_avoidance m Q F H A Z p ζh σ hhub j (Y j) (hYT j)
      (hdiv j) ((hchangeY j).trans hscale) e C Zdel hd
  · intro k C hC
    have hscale:ζ*(p*Fintype.card (V⊕U))≤ζe*(p*Fintype.card (V⊕U)):=
      mul_le_mul_of_nonneg_right hζe (by positivity)
    have hd (w:V⊕U):((C⊔Zdel).degree w:ℝ)≤ζe*(p*Fintype.card (V⊕U)):=by
      have hsum:((C⊔Zdel).degree w:ℝ)≤(C.degree w:ℝ)+Zdel.degree w:=by
        exact_mod_cast graph_degree_sup_le C Zdel w
      exact hsum.trans ((add_le_add (hC w) (hZ w)).trans (hbudgetE.trans hscale))
    obtain ⟨E,hE⟩:=hend k (S' k) (R' k) (C⊔Zdel) (hS k) (hR k)
      ((hchangeS k).trans hscale) ((hchangeR k).trans hscale)
      (by intro w;simpa only [←SimpleGraph.ncard_neighborSet] using hd w) (hratio k)
    exact ⟨E,hE.mono_right le_sup_left,hE.mono_right le_sup_right⟩
end Oberwolfach
