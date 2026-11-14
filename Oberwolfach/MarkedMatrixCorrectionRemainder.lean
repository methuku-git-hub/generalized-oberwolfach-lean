module

public import Oberwolfach.MarkedMatrixDivisibility
public import Oberwolfach.MarkedFiniteRemainderTransfer
public import Oberwolfach.MarkedOldInnerAgreement

@[expose] public section

/-! Preserve the original finite occurrence identifiers after the sparse
matrix correction. The retained spoke is classified by its original type.
Zero allowed entries on the protected pair exclude every deleted edge there. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_matrix_correction_finite_divisible
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (m:ℕ)
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (J₀ Jₖ:V→V→ℕ) (L₀ Lₖ:V→U→ℕ)
    (hbal:TypedMatrixBalanced m
      (occurrenceMultiplicity (fun e:{e // J₀ (tail e) (head e)=0}=>tail e.val) (fun e=>head e.val))
      (occurrenceMultiplicity (fun e:{e // Jₖ (ktail e) (khead e)=0}=>ktail e.val) (fun e=>khead e.val))
      (relationMultiplicity (fun v u=>H₀ v u∧L₀ v u=0))
      (relationMultiplicity (fun v u=>HK v u∧Lₖ v u=0))):
    MarkedRemainderDivisible tail head ktail khead HK
      (Finset.univ.filter (Sum.elim (fun e=>J₀ (tail e) (head e)=0) (fun e=>Jₖ (ktail e) (khead e)=0)))
      (Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∧L₀ z.1 z.2=0)∨(HK z.1 z.2∧Lₖ z.1 z.2=0))) m:=by
  let PE:=fun e:E=>J₀ (tail e) (head e)=0
  let PK:=fun e:K=>Jₖ (ktail e) (khead e)=0
  let H₀':=fun v u=>H₀ v u∧L₀ v u=0
  let HK':=fun v u=>HK v u∧Lₖ v u=0
  let S:=Finset.univ.filter (fun z:V×U=>H₀' z.1 z.2∨HK' z.1 z.2)
  have h:=marked_matrix_balanced_divisible
    (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
    (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) H₀' HK' m
    (fun v u h=>hH v u ⟨h.1.1,h.2.1⟩) hbal
  let A:Finset ({e // PE e}⊕{e // PK e}):=Finset.univ
  let f:A→E⊕K:=fun a=>Sum.map Subtype.val Subtype.val a.val
  have hf:Function.Injective f:=
    (Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩).comp Subtype.val_injective
  have hsp:∀ z∈S,HK z.1 z.2↔HK' z.1 z.2:=by
    intro z hz
    constructor
    · intro hk
      rcases (Finset.mem_filter.mp hz).2 with h0|hk'
      · exact (hH z.1 z.2 ⟨h0.1,hk⟩).elim
      · exact hk'
    · exact And.left
  have hi:Finset.univ.image f=
      Finset.univ.filter (Sum.elim PE PK):=by
    ext a
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_filter]
    constructor
    · rintro ⟨a',rfl⟩
      dsimp only [f]
      cases a'.val with
      | inl e=>exact e.property
      | inr e=>exact e.property
    · intro ha
      cases a with
      | inl e=>exact ⟨⟨Sum.inl ⟨e,ha⟩,Finset.mem_univ _⟩,rfl⟩
      | inr e=>exact ⟨⟨Sum.inr ⟨e,ha⟩,Finset.mem_univ _⟩,rfl⟩
  have h':MarkedRemainderDivisible tail head ktail khead HK (Finset.univ.image f) S m:=by
    apply marked_finite_remainder_image_divisible
      (tail:=fun e:{e // PE e}=>tail e.val) (head:=fun e=>head e.val)
      (ktail:=fun e:{e // PK e}=>ktail e.val) (khead:=fun e=>khead e.val) A S f hf
    · intro a;dsimp only [f];cases a.val <;> rfl
    · intro a;dsimp only [f];cases a.val <;> rfl
    · intro a;dsimp only [f];cases a.val <;> rfl
    · exact hsp
    · convert h using 1 <;> congr!
  rw [hi] at h'
  exact h'

theorem marked_matrix_deletion_avoids_protected_pair
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (H₀ HK:V→U→Prop) (J₀ Jₖ:V→V→ℕ) (L₀ Lₖ:V→U→ℕ)
    (T:Finset V) (W:Finset U) (hT:∀ v,π v∈T↔v∈T)
    (hJ₀:∀ v∈T,∀ w∈T,J₀ v w=0) (hJₖ:∀ v∈T,∀ w∈T,Jₖ v w=0)
    (hL₀:∀ v∈T,∀ u∈W,L₀ v u=0) (hLₖ:∀ v∈T,∀ u∈W,Lₖ v u=0):
    let A:=Finset.univ.filter (Sum.elim (fun e=>J₀ (tail e) (head e)≠0) (fun e=>Jₖ (ktail e) (khead e)≠0))
    let S:=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∧L₀ z.1 z.2≠0)∨(HK z.1 z.2∧Lₖ z.1 z.2≠0))
    (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr).filter
      (markedInnerResource T W)=∅:=by
  intro A S
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hr,hi⟩:=Finset.mem_filter.mp hr
  rcases Finset.mem_union.mp hr with hr|hr
  · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hr
    have hh:=(marked_physical_edge_inner_iff T hT a).mp hi
    have ha':=(Finset.mem_filter.mp ha).2
    cases a with
    | inl e=>exact ha' (hJ₀ _ hh.1 _ hh.2)
    | inr e=>exact ha' (hJₖ _ hh.1 _ hh.2)
  · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hr
    rcases (Finset.mem_filter.mp hz).2 with hz|hz
    · exact hz.2 (hL₀ _ hi.1 _ hi.2)
    · exact hz.2 (hLₖ _ hi.1 _ hi.2)

end Oberwolfach
