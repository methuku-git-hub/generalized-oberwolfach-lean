module

public import Oberwolfach.RetainedIncidenceSets

@[expose] public section

/-! Physical coordinates attached to one outside index and one inner label.
The support also includes the label's supplied successor. One physical
coordinate belongs to one outside index and affects at most two labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A J V E:Type*} [Fintype A] [Fintype J] [Fintype V] [Fintype E]
  [DecidableEq A] [DecidableEq J] [DecidableEq V] [DecidableEq E]

def boundaryLabelCoordinates (coin:A↪E) (owner:A→J) (label:A→V) (π:Equiv.Perm V)
    (j:J) (v:V):Finset E :=
  (Finset.univ.filter (fun a=>owner a=j∧(label a=v∨π (label a)=v))).image coin

theorem boundaryLabelCoordinates_mem (coin:A↪E) (owner:A→J) (label:A→V) (π:Equiv.Perm V)
    (j:J) (v:V) (e:E):
    e∈boundaryLabelCoordinates coin owner label π j v ↔
      ∃ a,owner a=j∧(label a=v∨π (label a)=v)∧coin a=e := by
  simp only [boundaryLabelCoordinates,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  aesop

theorem boundaryLabelCoordinates_distinct_owners (coin:A↪E) (owner:A→J) (label:A→V) (π:Equiv.Perm V)
    (i j:J) (hij:i≠j) (v w:V):
    Disjoint (boundaryLabelCoordinates coin owner label π i v)
      (boundaryLabelCoordinates coin owner label π j w) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨a,ha,_,he⟩:=(boundaryLabelCoordinates_mem coin owner label π i v e).mp he
  obtain ⟨b,hb,_,hf⟩:=(boundaryLabelCoordinates_mem coin owner label π j w e).mp hf
  have hab:=coin.injective (he.trans hf.symm)
  subst b
  exact hij (ha.symm.trans hb)

theorem boundaryLabelCoordinates_influence (coin:A↪E) (owner:A→J) (label:A→V) (π:Equiv.Perm V)
    (j:J) (e:E):
    (Finset.univ.filter (fun v=>e∈boundaryLabelCoordinates coin owner label π j v)).card≤2 := by
  by_cases hex:∃ a,coin a=e
  · obtain ⟨a,ha⟩:=hex
    have hs:Finset.univ.filter (fun v=>e∈boundaryLabelCoordinates coin owner label π j v)⊆
        {label a,π (label a)} := by
      intro v hv
      obtain ⟨b,_,hb,he⟩:=(boundaryLabelCoordinates_mem coin owner label π j v e).mp (Finset.mem_filter.mp hv).2
      have hab:=coin.injective (he.trans ha.symm)
      subst b
      simpa only [Finset.mem_insert,Finset.mem_singleton,eq_comm] using hb
    exact (Finset.card_le_card hs).trans (by simpa using Finset.card_insert_le (label a) {π (label a)})
  · have he:Finset.univ.filter (fun v=>e∈boundaryLabelCoordinates coin owner label π j v)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨a,_,_,ha⟩:=(boundaryLabelCoordinates_mem coin owner label π j v e).mp (Finset.mem_filter.mp hv).2
      exact hex ⟨a,ha⟩
    simp [he]

theorem boundaryLabelCoordinates_read (coin:A↪E) (owner:A→J) (label:A→V) (π:Equiv.Perm V)
    (K:ℕ) (hfiber:∀ j v,(Finset.univ.filter (fun a=>owner a=j∧label a=v)).card≤K)
    (j:J) (v:V):
    (boundaryLabelCoordinates coin owner label π j v).card≤2*K := by
  let F:=fun w=>Finset.univ.filter (fun a=>owner a=j∧label a=w)
  have he:Finset.univ.filter (fun a=>owner a=j∧(label a=v∨π (label a)=v))=
      F v∪F (π.symm v) := by
    ext a
    simp only [F,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    have hh:π (label a)=v ↔ label a=π.symm v:=by
      constructor
      · intro h;simpa using congrArg π.symm h
      · intro h;rw [h,π.apply_symm_apply]
    rw [hh];tauto
  unfold boundaryLabelCoordinates
  rw [he]
  exact (Finset.card_image_le).trans ((Finset.card_union_le _ _).trans (by
    have h₁:=hfiber j v;have h₂:=hfiber j (π.symm v);dsimp [F];omega))

theorem retained_boundary_label_support (coin:A↪E) (owner:A→J) (label:A→V) (π:Equiv.Perm V)
    (σ:E→Bool) (j:J):
    retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) σ j=
      (Finset.univ.filter (fun a=>owner a=j∧σ (coin a)=true)).image label∪
      ((Finset.univ.filter (fun a=>owner a=j∧σ (coin a)=true)).image label).image π := by
  ext v
  simp only [mem_retainedIncidenceSet,boundaryLabelCoordinates_mem,Finset.mem_union,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,⟨a,ha,hv,he⟩,hσ⟩
    have hs:σ (coin a)=true:=he ▸ hσ
    rcases hv with hv|hv
    · exact Or.inl ⟨a,⟨ha,hs⟩,hv⟩
    · exact Or.inr ⟨label a,⟨a,⟨ha,hs⟩,rfl⟩,hv⟩
  · rintro (⟨a,⟨ha,hs⟩,hv⟩|⟨w,⟨a,⟨ha,hs⟩,hw⟩,hv⟩)
    · exact ⟨coin a,⟨a,ha,Or.inl hv,rfl⟩,hs⟩
    · exact ⟨coin a,⟨a,ha,Or.inr (by rw [hw];exact hv),rfl⟩,hs⟩

end Oberwolfach
