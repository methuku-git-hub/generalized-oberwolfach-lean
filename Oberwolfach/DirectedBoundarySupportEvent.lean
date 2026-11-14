module

public import Oberwolfach.DirectedBoundaryIncidences
public import Oberwolfach.RetainedIncidenceCommonEvent

@[expose] public section

/-! The boundary support event derived from actual directed edge types and
injective physical coordinates. Each edge keeps its original type and
orientation; only its physical coordinate is sampled. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A W E:Type*} [Fintype A] [Fintype W] [Fintype E]
  [DecidableEq A] [DecidableEq W] [DecidableEq E]

def directedBoundarySupport (tail head:A→W) (coin:A→E) (X:Finset W)
    (π:Equiv.Perm W) (σ:E→Bool) (x:W):Finset W :=
  let F:=Finset.univ.filter (fun a:DirectedBoundaryEdge tail head X=>
    boundaryOutside tail head X a=x∧σ (coin a.val)=true)
  F.image (boundaryInside tail head X)∪(F.image (boundaryInside tail head X)).image π

theorem directedBoundarySupport_incidence (tail head:A→W) (coin:A↪E) (X:Finset W)
    (π:Equiv.Perm W) (σ:E→Bool) (x:W):
    directedBoundarySupport tail head coin X π σ x=
      retainedIncidenceSet
        (boundaryLabelCoordinates ((Function.Embedding.subtype _).trans coin)
          (boundaryOutside tail head X) (boundaryInside tail head X) π) σ x := by
  symm
  exact retained_boundary_label_support _ _ _ _ _ _

theorem directedBoundarySupport_subset (tail head:A→W) (coin:A→E) (X:Finset W)
    (π:Equiv.Perm W) (hX:∀ x∈X,π x∈X) (σ:E→Bool) (x:W):
    directedBoundarySupport tail head coin X π σ x⊆X := by
  intro y hy
  rcases Finset.mem_union.mp hy with hy|hy
  · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hy
    exact boundaryInside_mem tail head X a
  · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hy
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hz
    exact hX _ (boundaryInside_mem tail head X a)

theorem directedBoundarySupport_empty_at_inner (tail head:A→W) (coin:A→E) (X:Finset W)
    (π:Equiv.Perm W) (σ:E→Bool) (x:W) (hx:x∈X):
    directedBoundarySupport tail head coin X π σ x=∅ := by
  have he:Finset.univ.filter (fun a:DirectedBoundaryEdge tail head X=>
      boundaryOutside tail head X a=x∧σ (coin a.val)=true)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hax:boundaryOutside tail head X a=x:=(Finset.mem_filter.mp ha).2.1
    exact boundaryOutside_notMem tail head X a (hax.symm ▸ hx)
  simp only [directedBoundarySupport,he,Finset.image_empty,Finset.union_empty]

theorem directed_boundary_support_common_event (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ):
    ∃ N:ℕ,∀ (A W E T:Type) [Fintype A] [DecidableEq A] [Fintype W] [DecidableEq W]
      [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T],
    N≤Fintype.card W→Fintype.card T≤3→
    ∀ (tail head:A→W) (kind:A→T) (coin:A↪E) (X:Finset W) (π:Equiv.Perm W),
      Function.Injective (fun a=>(kind a,tail a,head a))→
      1-1/(Fintype.card W:ℝ)^q≤
        (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>
            (∀ x,((directedBoundarySupport tail head coin X π σ x).card:ℝ)≤13*p*Fintype.card W)∧
            (∀ x y,x≠y→((directedBoundarySupport tail head coin X π σ x∩
              directedBoundarySupport tail head coin X π σ y).card:ℝ)≤145*p^2*Fintype.card W)∧
            (∀ v,((Finset.univ.filter (fun x=>v∈directedBoundarySupport tail head coin X π σ x)).card:ℝ)≤
              13*p*Fintype.card W)) := by
  obtain ⟨N,hN⟩:=retained_incidence_support_common_event 12 (p^2) (by norm_num) (by positivity) q
  refine ⟨N,?_⟩
  intro A W E T _ _ _ _ _ _ _ _ hn hT tail head kind coin X π hinj
  let C:=boundaryLabelCoordinates ((Function.Embedding.subtype _).trans coin)
    (boundaryOutside tail head X) (boundaryInside tail head X) π
  have hf (x y:W):(Finset.univ.filter (fun a:DirectedBoundaryEdge tail head X=>
      boundaryOutside tail head X a=x∧boundaryInside tail head X a=y)).card≤6 :=
    (boundary_owner_label_fibre tail head kind X hinj x y).trans (by omega)
  have hr (x y:W):((C x y).card:ℝ)≤12 := by
    have hh:=boundaryLabelCoordinates_read ((Function.Embedding.subtype _).trans coin)
      (boundaryOutside tail head X) (boundaryInside tail head X) π 6 hf x y
    exact_mod_cast hh
  have ha (x:W) (e:E):((Finset.univ.filter (fun y=>e∈C x y)).card:ℝ)≤12 := by
    have hh:=boundaryLabelCoordinates_influence ((Function.Embedding.subtype _).trans coin)
      (boundaryOutside tail head X) (boundaryInside tail head X) π x e
    exact (by exact_mod_cast hh : ((Finset.univ.filter (fun y=>e∈C x y)).card:ℝ)≤2).trans (by norm_num)
  have hd (x y:W) (hxy:x≠y) (v:W):Disjoint (C x v) (C y v):=
    boundaryLabelCoordinates_distinct_owners _ _ _ _ x y hxy v v
  have hh:=hN (Fintype.card W) hn W W E (le_refl _) (le_refl _) C hr ha hd p hp.le hp1
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  have he (x:W):directedBoundarySupport tail head coin X π σ x=retainedIncidenceSet C σ x:=
    directedBoundarySupport_incidence tail head coin X π σ x
  simp only [he]
  have hpn:p^2*Fintype.card W≤p*Fintype.card W :=
    mul_le_mul_of_nonneg_right (by nlinarith : p^2≤p) (Nat.cast_nonneg _)
  refine ⟨?_,?_,?_⟩
  · intro x;have hx:=hσ.1 x;linarith
  · intro x y hxy;have hx:=hσ.2.1 x y hxy;linarith
  · intro v;have hx:=hσ.2.2 v;linarith

end Oberwolfach
