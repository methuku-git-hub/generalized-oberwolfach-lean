module

public import Oberwolfach.MarkedFiniteDeletionDegrees
public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section

/-! The reserved star vanishes on the active vertex/hub pair. Restricting
its actual physical deletion therefore gives exactly the same outcome as
restricting the later packings' deletion alone. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V₀ U₀ Γ Color:Type} [Fintype V] [Fintype U] [Fintype V₀] [Fintype U₀]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder V₀] [DecidableEq U] [DecidableEq U₀]

theorem marked_reserved_star_active_graphs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (T:Finset V) (W:Finset U) (hT:∀ x,π x∈T↔x∈T)
    (f:V₀→V) (g:U₀→U) (hf:∀ x,f x∉T) (hg:∀ u,g u∉W):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    ∀ (KA:Finset (E₀⊕E₁)) (KS:Finset (V×U)),
    (∀ a∈KA,Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a∈T∨
      Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a∈T)→
    (∀ z∈KS,z.1∈T∨z.2∈W)→
    (markedSampleArcSetGraph P π d σ KA).comap f=⊥ ∧
    (markedFiniteSpokeGraph KS).comap (Sum.map f g)=⊥:=by
  intro E₀ E₁ KA KS hKA hKS
  have hR (x y:V₀):¬(markedSampleArcSetGraph P π d σ KA).Adj (f x) (f y):=by
    intro h
    obtain ⟨a,ha,he⟩:=Finset.mem_image.mp h.2
    have hz:∃z∈({f x,f y}:Finset V),z∈T:=by
      rw [←he]
      have hh:=hKA a ha
      cases a with
      | inl a=>
        rcases hh with hx|hy
        · exact ⟨a.val.1,by simp [markedPhysicalEdge],hx⟩
        · exact ⟨a.val.2,by simp [markedPhysicalEdge],hy⟩
      | inr a=>
        rcases hh with hx|hy
        · exact ⟨a.val.1,by simp [markedPhysicalEdge],hx⟩
        · exact ⟨π a.val.2,by simp [markedPhysicalEdge],(hT _).mpr hy⟩
    obtain ⟨z,hz,hzT⟩:=hz
    rcases Finset.mem_insert.mp hz with hz|hz
    · exact hf x (hz ▸ hzT)
    · exact hf y ((Finset.mem_singleton.mp hz) ▸ hzT)
  have hS (x:V₀) (u:U₀):¬(markedFiniteSpokeGraph KS).Adj (Sum.inl (f x)) (Sum.inr (g u)):=by
    intro h
    rcases hKS (f x,g u) ((markedFiniteSpokeGraph_adj KS _ _).mp h) with h|h
    · exact hf x h
    · exact hg u h
  constructor
  · ext x y
    simp only [SimpleGraph.comap_adj,SimpleGraph.bot_adj,hR]
  · ext x y
    cases x <;> cases y
    · simp only [SimpleGraph.comap_adj,Sum.map_inl,SimpleGraph.bot_adj,
        (markedFiniteSpokeGraph_same_part KS).1]
    · simp only [SimpleGraph.comap_adj,Sum.map_inl,Sum.map_inr,SimpleGraph.bot_adj,hS]
    · simp only [SimpleGraph.comap_adj,Sum.map_inl,Sum.map_inr,SimpleGraph.bot_adj]
      exact iff_false_intro (fun h=>hS _ _ h.symm)
    · simp only [SimpleGraph.comap_adj,Sum.map_inr,SimpleGraph.bot_adj,
        (markedFiniteSpokeGraph_same_part KS).2]

theorem rawMarked_active_reservation_deletion
    (f:V₀→V) (g:U₀→U) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (KR DR:SimpleGraph V) (KS DS:SimpleGraph (V⊕U))
    (hKR:KR.comap f=⊥) (hKS:KS.comap (Sum.map f g)=⊥):
    rawMarkedRestrictPair f g (rawMarkedDeleteRims σ (KR⊔DR).edgeFinset)=
      rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset) ∧
    (fun b x u=>markedDeletePhysicalSpokes H (KS⊔DS) b (f x) (g u))=
      (fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u)):=by
  have hR:(KR⊔DR).comap f=DR.comap f:=by
    ext x y
    have hh:¬KR.Adj (f x) (f y):=by
      have hbot:¬(KR.comap f).Adj x y:=by rw [hKR];simp
      exact hbot
    simp only [SimpleGraph.comap_adj,SimpleGraph.sup_adj,hh,false_or]
  have hS:∀ x u,¬KS.Adj (Sum.inl (f x)) (Sum.inr (g u)):=by
    intro x u
    have hbot:¬(KS.comap (Sum.map f g)).Adj (Sum.inl x) (Sum.inr u):=by rw [hKS];simp
    exact hbot
  constructor
  · have hK:=rawMarkedRestrictPair_deleteRims f g σ (KR⊔DR)
    have hD:=rawMarkedRestrictPair_deleteRims f g σ DR
    calc
      _ = rawMarkedDeleteRims (rawMarkedRestrictPair f g σ) ((KR⊔DR).comap f).edgeFinset:=by
        convert hK using 1 <;> congr!
      _ = rawMarkedDeleteRims (rawMarkedRestrictPair f g σ) (DR.comap f).edgeFinset:=by
        congr 1
        ext e
        simp only [SimpleGraph.mem_edgeFinset,hR]
      _ = _ :=hD.symm
  · funext b x u
    apply propext
    simp only [markedDeletePhysicalSpokes,SimpleGraph.sup_adj,hS,false_or]

end Oberwolfach
