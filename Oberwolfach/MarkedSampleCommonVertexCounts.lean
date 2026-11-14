module

public import Oberwolfach.MarkedConfigurationVertexTransport
public import Oberwolfach.MarkedPhysicalCutTransfer
public import Oberwolfach.CanonicalMarkedPathSpokeChanges

@[expose] public section

/-! Removing vertices from the actual sample loses only configurations
using removed free coordinates. Root spokes are still omitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem markedSampleArc_restrictPair_exists_iff
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (mark:Bool) (x y:W):
    (∃ e:MarkedSampleArc (P.comap f) ρ (3*d) (fun a=>rawMarkedRestrictPair f g σ (Sum.inl a)) mark,
      e.val.1=x∧e.val.2=y)↔
    (∃ e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) mark,e.val.1=f x∧e.val.2=f y):=by
  rw [markedSampleArc_indicator_iff,markedSampleArc_indicator_iff,markedPhysicalRim_restrictPair_eq f g π ρ hf P d σ mark x y]

theorem spoke_domain_change_bound (H:Bool→V→U→Prop) (A:Finset V):
    ∀ mark u,(∑ x,if ¬(H mark x u↔H mark x u∧x∈A) then (1:ℝ) else 0)≤(Finset.univ\A).card:=by
  intro mark u
  calc
    _ ≤ ∑ x:V,if x∉A then (1:ℝ) else 0:=by
      apply Finset.sum_le_sum
      intro x _
      by_cases h:H mark x u <;> by_cases hx:x∈A <;> simp [h,hx]
    _ = _:=by
      have he:(Finset.univ\A)=(Finset.univ.filter (fun x:V=>x∉A)):=by ext;simp
      rw [he]
      simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem marked_sample_common_cycle_vertex_loss
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (u u':Z):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let σA:=rawMarkedRestrictPair f g σ
    let EA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let KA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true;
    (Fintype.card (CommonMarkedCycle (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      m π (3*d) (H false) (H true) (g u) (g u')):ℝ)-
    Fintype.card (CommonMarkedCycle (fun e:EA=>e.val.1) (fun e=>e.val.2) (fun e:KA=>e.val.1) (fun e=>e.val.2)
      m ρ (3*d) (fun x v=>H false (f x) (g v)) (fun x v=>H true (f x) (g v)) u u')≤
      2*((m:ℝ)+1)*(Finset.univ\Finset.univ.image f).card*(Fintype.card V:ℝ)^m:=by
  intro E K σA EA KA
  let A:=Finset.univ.image f
  let H':=fun mark x v=>H mark x v∧x∈A
  have hc:=commonMarkedCycle_spoke_changes (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) H H' (g u) (g u')
    (Finset.univ\A).card (by
      intro b v
      convert spoke_domain_change_bound H A b v using 1 <;> congr!)
  have hH (mark:Bool) (x:W) (v:Z):H mark (f x) (g v)↔H' mark (f x) (g v):=by simp [H',A]
  have he:=commonMarkedCycle_vertex_card (m:=m) (b:=3*d) f.toEmbedding g hf
    (markedSampleArc_restrictPair_exists_iff f g π ρ hf P d σ false)
    (markedSampleArc_restrictPair_exists_iff f g π ρ hf P d σ true)
    (fun x v=>H false (f x) (g v)) (fun x v=>H true (f x) (g v)) (H' false) (H' true)
    (hH false) (hH true) u u' (by
      intro C i
      have hi:=(markedHubCompatible_iff_positions _ _ _ _).mp C.property.1 i
      have hm:C.val.val i∈A:=by
        cases h:markedPositionType i <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at hi <;> exact hi.2
      obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hm
      exact ⟨x,hx⟩)
  have hfcoe (v:W):f.toEmbedding v=f v:=rfl
  try simp only [hfcoe] at he
  simp only [Fintype.card_eq_nat_card] at he hc ⊢
  rw [←he] at hc
  exact hc

theorem marked_sample_common_path_vertex_loss
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (i:Fin (m+1)) (x x':W) (u u':Z):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let σA:=rawMarkedRestrictPair f g σ
    let EA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let KA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true;
    (Fintype.card (CanonicalCommonMarkedPath (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      m π (3*d) (H false) (H true) i (f x) (f x') (g u) (g u')):ℝ)-
    Fintype.card (CanonicalCommonMarkedPath (fun e:EA=>e.val.1) (fun e=>e.val.2) (fun e:KA=>e.val.1) (fun e=>e.val.2)
      m ρ (3*d) (fun x v=>H false (f x) (g v)) (fun x v=>H true (f x) (g v)) i x x' u u')≤
      2*(m:ℝ)*(Finset.univ\Finset.univ.image f).card*(Fintype.card V:ℝ)^(m-1):=by
  intro E K σA EA KA
  let A:=Finset.univ.image f
  let H':=fun mark x v=>H mark x v∧x∈A
  have hc:=canonicalCommonMarkedPath_spoke_changes (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) H H' i (f x) (f x') (g u) (g u')
    (Finset.univ\A).card (by
      intro b v
      convert spoke_domain_change_bound H A b v using 1 <;> congr!)
  have hH (mark:Bool) (x:W) (v:Z):H mark (f x) (g v)↔H' mark (f x) (g v):=by simp [H',A]
  have he:=canonicalCommonMarkedPath_vertex_card (m:=m) (b:=3*d) f.toEmbedding g hf
    (markedSampleArc_restrictPair_exists_iff f g π ρ hf P d σ false)
    (markedSampleArc_restrictPair_exists_iff f g π ρ hf P d σ true)
    (fun x v=>H false (f x) (g v)) (fun x v=>H true (f x) (g v)) (H' false) (H' true)
    (hH false) (hH true) i x x' u u' (by
      intro z a
      have hi:=(z.property.2.2 a).1
      have hm:z.val a∈A:=by
        cases h:markedPositionType (i.succAbove a) <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at hi <;> exact hi.2
      obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hm
      exact ⟨x,hx⟩)
  have hfcoe (v:W):f.toEmbedding v=f v:=rfl
  try simp only [hfcoe] at he
  simp only [Fintype.card_eq_nat_card] at he hc ⊢
  rw [←he] at hc
  exact hc

end Oberwolfach
