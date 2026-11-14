module

public import Oberwolfach.MarkedSampleCommonVertexCounts
public import Oberwolfach.MarkedSampleCommonPhysicalDeletion

@[expose] public section

/-! Full common-cycle and root-omitted common-path transfers to the actual
active sample. Vertex loss and physical edge loss are charged separately
at their original and active orders, respectively. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_protected_active_common_configurations
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d m:ℕ) (hm:1≤m)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (δ:ℝ)
    (hDR:∀ x,((DR.comap f).degree x:ℝ)≤δ)
    (hDS:∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤δ):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let HA:=fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u)
    let EA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let KA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true;
    (∀ u u':Z,
      (Fintype.card (CommonMarkedCycle (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        m π (3*d) (H false) (H true) (g u) (g u')):ℝ)-
      Fintype.card (CommonMarkedCycle (fun e:EA=>e.val.1) (fun e=>e.val.2) (fun e:KA=>e.val.1) (fun e=>e.val.2)
        m ρ (3*d) (HA false) (HA true) u u')≤
        2*((m:ℝ)+1)*(Finset.univ\Finset.univ.image f).card*(Fintype.card V:ℝ)^m+
        3*((m:ℝ)+1)*δ*(Fintype.card W:ℝ)^m)∧
    (∀ (i:Fin (m+1)) (x x':W) (u u':Z),
      (Fintype.card (CanonicalCommonMarkedPath (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        m π (3*d) (H false) (H true) i (f x) (f x') (g u) (g u')):ℝ)-
      Fintype.card (CanonicalCommonMarkedPath (fun e:EA=>e.val.1) (fun e=>e.val.2) (fun e:KA=>e.val.1) (fun e=>e.val.2)
        m ρ (3*d) (HA false) (HA true) i x x' u u')≤
        2*(m:ℝ)*(Finset.univ\Finset.univ.image f).card*(Fintype.card V:ℝ)^(m-1)+
        4*((m:ℝ)+1)*δ*(Fintype.card W:ℝ)^(m-1)):=by
  intro E K σA HA EA KA
  let σ₀:=rawMarkedRestrictPair f g σ
  let H₀:=fun b x u=>H b (f x) (g u)
  have hσ:rawMarkedDeleteRims σ₀ (DR.comap f).edgeFinset=σA:=
    (rawMarkedRestrictPair_deleteRims f g σ DR).symm
  have hH:markedDeletePhysicalSpokes H₀ (DS.comap (Sum.map f g))=HA:=rfl
  constructor
  · intro u u'
    have hv:=marked_sample_common_cycle_vertex_loss f g π ρ hf P d m σ H u u'
    have hd:=marked_sample_common_cycle_physical_deletion (P.comap f) ρ d m hm σ₀ H₀
      (DR.comap f) (DS.comap (Sum.map f g)) δ hDR hDS u u'
    dsimp only at hv hd
    simp only [hσ,hH] at hd
    dsimp only [E,K,EA,KA,σA,σ₀,H₀,HA] at hv hd ⊢
    simp only [rawMarkedRestrictPair_deleteRims,markedDeletePhysicalSpokes,SimpleGraph.comap_adj,Sum.map_inl,Sum.map_inr,
      Fintype.card_eq_nat_card] at hv hd ⊢
    have hsum:=add_le_add hv hd
    convert hsum using 1 <;> ring_nf <;> congr! <;> exact rawMarkedRestrictPair_deleteRims f g σ DR
  · intro i x x' u u'
    have hv:=marked_sample_common_path_vertex_loss f g π ρ hf P d m σ H i x x' u u'
    have hd:=marked_sample_common_path_physical_deletion (P.comap f) ρ d m hm σ₀ H₀
      (DR.comap f) (DS.comap (Sum.map f g)) δ hDR hDS i x x' u u'
    dsimp only at hv hd
    simp only [hσ,hH] at hd
    dsimp only [E,K,EA,KA,σA,σ₀,H₀,HA] at hv hd ⊢
    simp only [rawMarkedRestrictPair_deleteRims,markedDeletePhysicalSpokes,SimpleGraph.comap_adj,Sum.map_inl,Sum.map_inr,
      Fintype.card_eq_nat_card] at hv hd ⊢
    have hsum:=add_le_add hv hd
    convert hsum using 1 <;> ring_nf <;> congr! <;> exact rawMarkedRestrictPair_deleteRims f g σ DR

end Oberwolfach
