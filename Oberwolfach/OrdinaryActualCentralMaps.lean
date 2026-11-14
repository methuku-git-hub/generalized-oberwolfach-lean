module

public import Oberwolfach.OrdinaryActualFiniteModels
public import Oberwolfach.OrdinaryReindexResourceMaps

@[expose] public section

/-! Actual embedded expansion-to-central edge bijections. Reindexing
allows the expansions of the original graph and its decomposable
comparison graph to have precisely the same central image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ E J W V U : Type}
    [Fintype V₀] [Fintype U₀] [Fintype E] [Fintype J] [Fintype W] [Fintype V] [Fintype U]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq E] [DecidableEq J] [DecidableEq W] [DecidableEq V] [DecidableEq U]

def actualCentralRowMap (G : SimpleGraph V₀) (H : V₀ → U₀ → Prop)
    (e : G.edgeFinset≃E) (j : ActualSpoke H≃J) :
    ActualExpansionRow G H W → ExpansionRow Unit E J W :=
  expansionReindexRow e j ∘ expansionRowMap (fun _ : V₀ => ())

def actualCentralHubMap (G : SimpleGraph V₀) (H : V₀ → U₀ → Prop)
    (e : G.edgeFinset≃E) (j : ActualSpoke H≃J) :
    ActualExpansionHub G H → ExpansionHub Unit E J :=
  expansionReindexHub e j ∘ expansionHubMap (fun _ : U₀ => ())

theorem actual_embedded_expansion_central_bijection
    (G : SimpleGraph V₀) (H : V₀ → U₀ → Prop) (C : SimpleGraph W) (z o : W) (hzo : z≠o)
    (e : G.edgeFinset≃E) (j : ActualSpoke H≃J)
    (i : ActualExpansionRow G H W ↪ V) (i' : ExpansionRow Unit E J W ↪ V)
    (s : ActualExpansionHub G H ↪ U) (s' : ExpansionHub Unit E J ↪ U) :
    let Q₀ := (actualExpansionRim G H C z o).map i
    let K₀ := ordinaryMappedSpokes (actualExpansionSpokes G H z) i s
    let Q₁ := (ordinaryExpansionRim (J:=J) C z o (fun _ : E => ()) (fun _ => ())).map i'
    let K₁ := ordinaryMappedSpokes (ordinaryExpansionSpokes (E:=E) z (fun _ : J => ()) (fun _ => ())) i' s'
    let f := ordinaryAmbientMap i i' (actualCentralRowMap G H e j)
    let g := ordinaryAmbientMap s s' (actualCentralHubMap G H e j)
    Set.InjOn (ordinaryPairResourceMap f g) (ordinaryHostResources Q₀ K₀) ∧
      transformerImageResources Q₀ K₀ f g=ordinaryHostResources Q₁ K₁ ∧
      Function.Injective (fun e:Q₀.edgeFinset => s(f e.val.out.1,f e.val.out.2)) ∧
      Function.Injective (fun e:{p:V×U // K₀ p.1 p.2} => (f e.val.1,g e.val.2)) ∧
      (∀ v w,Q₀.Adj v w → Q₁.Adj (f v) (f w)) ∧ ∀ v u,K₀ v u → K₁ (f v) (g u) := by
  dsimp only
  have hmaps : ordinaryPairResourceMap (actualCentralRowMap (W:=W) G H e j) (actualCentralHubMap G H e j)=
      expansionReindexResource (V:=Unit) (U:=Unit) (W:=W) e j ∘
        expansionResourceMap (E:=G.edgeFinset) (J:=ActualSpoke H) (W:=W) (fun _ : V₀ => ()) (fun _ : U₀ => ()) := by
    funext a
    cases a with
    | inl a => induction a using Sym2.ind with | _ v w => rfl
    | inr p => rfl
  have hfinite := ordinaryExpansion_common_central_resources C z o hzo
    (fun e:G.edgeFinset => e.val.out.1) (fun e:G.edgeFinset => e.val.out.2)
    (fun j:ActualSpoke H => j.val.1) (fun j:ActualSpoke H => j.val.2) e j
  have h := ordinaryAmbient_resource_bijection (actualExpansionRim G H C z o) (actualExpansionSpokes G H z)
    (ordinaryExpansionRim (J:=J) C z o (fun _ : E => ()) (fun _ => ()))
    (ordinaryExpansionSpokes (E:=E) z (fun _ : J => ()) (fun _ => ()))
    i i' s s' (actualCentralRowMap G H e j) (actualCentralHubMap G H e j)
    (by rw [hmaps];exact hfinite.1) (by
      rw [hmaps]
      ext a
      simpa only [Finset.mem_image] using Finset.ext_iff.mp hfinite.2 a)
  exact ⟨h.1,h.2,ordinary_resource_map_rim_injective _ _ _ _ h.1,
    ordinary_resource_map_spoke_injective _ _ _ _ h.1,
    ordinary_resource_image_rim_hom _ _ _ _ _ _ h.2,ordinary_resource_image_spoke_hom _ _ _ _ _ _ h.2⟩

end Oberwolfach
