module

public import Oberwolfach.MarkedHostExtensionCountsMonotone
public import Oberwolfach.MarkedHostCountsPhysicalDeletionReal
public import Oberwolfach.MarkedTypedLossFromSymmetricChanges

@[expose] public section
/-! Transfer lower extension counts to a changed host through the same
physical change graphs, allowing additions and deletions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_host_extensions_after_shared_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d l:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (c ch delta:ℝ) (hdelta:0≤delta) (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hrim:∀v,(FR.degree v:ℝ)≤delta) (hspoke:∀z,(FS.degree z:ℝ)≤delta)
    (hchange:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈FR.edgeFinset)
    (hspchange:∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true;
    MarkedHostExtensionCounts (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H false) (H true) π (3*d) l c ch →
    MarkedHostExtensionCounts (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) l
      (c-4*delta) (ch-(l+11)*delta):=by
  intro E K E' K' Q
  let σ₀:=rawMarkedDeleteRims σ FR.edgeFinset
  let H₀:=markedDeletePhysicalSpokes H FS
  let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ₀ (Sum.inl e)) false
  let K₀:=MarkedSampleArc P π (3*d) (fun e=>σ₀ (Sum.inl e)) true
  have hQ:=marked_sample_host_extensions_after_physical_deletion_real P π d l σ H c ch delta hdelta FR FS hrim hspoke Q
  have harc:∀j x y,markedArcPresent (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) j x y →
      markedArcPresent (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) j x y:=by
    intro j x y h
    cases j
    · simp only [markedArcPresent,Bool.false_eq_true,ite_false] at h ⊢
      obtain ⟨e,he₁,he₂⟩:=h
      subst x; subst y
      have he:markedPhysicalRim P π (3*d) (fun a=>τ (Sum.inl a)) false e.val.1 e.val.2=1:=by
        by_contra hn
        have hdel:markedPhysicalRim P π (3*d) (fun a=>σ (Sum.inl a)) false e.val.1 e.val.2=1 ∧
            s(e.val.1,e.val.2)∉FR.edgeFinset:=by
          simpa only [Bool.false_eq_true,ite_false] using (markedPhysicalRim_delete_iff P π d σ FR.edgeFinset false e.val.1 e.val.2).mp e.property
        have hc:=hchange (Sum.inl (e.val.1,e.val.2)) (by
          simp only [rawMarkedPairRims,Sum.elim_inl]
          exact fun iff=>hn (iff.mp hdel.1))
        simp only [markedPairPhysical,Sum.elim_inl] at hc
        exact hdel.2 hc
      exact ⟨⟨e.val,he⟩,rfl,rfl⟩
    · simp only [markedArcPresent,ite_true] at h ⊢
      obtain ⟨e,he₁,he₂⟩:=h
      subst x; subst y
      have he:markedPhysicalRim P π (3*d) (fun a=>τ (Sum.inl a)) true e.val.1 e.val.2=1:=by
        by_contra hn
        have hdel:markedPhysicalRim P π (3*d) (fun a=>σ (Sum.inl a)) true e.val.1 e.val.2=1 ∧
            s(e.val.1,π e.val.2)∉FR.edgeFinset:=by
          simpa only [ite_true] using (markedPhysicalRim_delete_iff P π d σ FR.edgeFinset true e.val.1 e.val.2).mp e.property
        have hc:=hchange (Sum.inr (e.val.1,e.val.2)) (by
          simp only [rawMarkedPairRims,Sum.elim_inr]
          exact fun iff=>hn (iff.mp hdel.1))
        simp only [markedPairPhysical,Sum.elim_inr] at hc
        exact hdel.2 hc
      exact ⟨⟨e.val,he⟩,rfl,rfl⟩
  have hH:∀b v u,H₀ b v u→H' b v u:=by
    intro b v u h
    change H b v u ∧ ¬FS.Adj (Sum.inl v) (Sum.inr u) at h
    by_contra hn
    exact h.2 (hspchange b v u (fun iff=>hn (iff.mp h.1)))
  exact marked_host_extension_counts_mono
    (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
    (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
    (H₀ false) (H₀ true) (H' false) (H' true) π (3*d) l _ _ harc (hH false) (hH true) hQ
end Oberwolfach
