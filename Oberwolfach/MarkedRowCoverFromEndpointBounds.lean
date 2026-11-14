module

public import Oberwolfach.MarkedAssignedRowPacking
public import Oberwolfach.MarkedAssignedArcDisjointness
public import Oberwolfach.MarkedTypedEndpointPairing

@[expose] public section

/-! An actual row cover: the endpoint matchings are constructed from the
five blocks, and every prescribed incoming arc, outgoing arc and root
spoke is covered by the resulting physically disjoint wheel family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T A B Y : Type} [Fintype V] [Fintype U] [Fintype A] [Fintype B] [Fintype Y]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : T → V} {H₀ HK : V → U → Prop}
    {π : Equiv.Perm V} {b l : ℕ} {c ch : ℝ}

theorem marked_row_cover_from_endpoint_bounds
    (Q : MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl : 2≤l) (hb : 1≤b)
    (hphys : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (F : Finset V) (hF : ∀ x, π x∈F ↔ x∈F) (v : V) (hv : v∉F)
    (N K M : ℕ) (hK : 0<K)
    (incoming : A ↪ E⊕T) (outgoing : B ↪ E⊕T) (hub : Y ↪ U) (jY : Y → Bool)
    (hA : Fintype.card A=N) (hB : Fintype.card B=N) (hY : Fintype.card Y=N)
    (hin : ∀ a, Sum.elim head khead (incoming a)=v)
    (hout : ∀ x, Sum.elim tail ktail (outgoing x)=v)
    (hFin : ∀ a, Sum.elim tail ktail (incoming a)∈F)
    (hFout : ∀ x, Sum.elim head khead (outgoing x)∈F)
    (hsepIn : ∀ a, ¬PermutationClose π b (Sum.elim tail ktail (incoming a)) v)
    (hsepOut : ∀ x, ¬PermutationClose π b (Sum.elim head khead (outgoing x)) v)
    (hSpoke : ∀ y, if jY y then HK v (hub y) else H₀ v (hub y))
    (hlabelIn : ∀ z, Fintype.card {a // Sum.elim tail ktail (incoming a)=z}≤M)
    (hlabelOut : ∀ z, Fintype.card {x // Sum.elim head khead (outgoing x)=z}≤M)
    (EA : A → Y → Prop) (EB : B → Y → Prop)
    (hEA : ∀ a y, EA a y → H₀ (Sum.elim tail ktail (incoming a)) (hub y))
    (hEB : ∀ x y, EB x y → if (outgoing x).isRight then
      HK (Sum.elim head khead (outgoing x)) (hub y) else H₀ (Sum.elim head khead (outgoing x)) (hub y))
    (hallowed : ∀ x y, EB x y → (outgoing x).isRight=true → jY y≠true)
    (hclass : Fintype.card {a // (incoming a).isRight=true}=Fintype.card {y // jY y=true})
    (d τ lam : ℝ) (hτ : 0<τ) (hlam : 0<lam)
    (hdegree : 2*τ+(M*(2*b+1):ℕ)≤d) (hmargin : (M*(2*b+1):ℕ)<lam*τ)
    (hgap : ((Finset.univ.filter (fun x => (outgoing x).isRight=true)).card:ℝ)+2*τ≤
      (Finset.univ.filter (fun y => ¬jY y=true)).card)
    (B₁ : BipartiteBlockBounds EA (fun a => (incoming a).isRight=true) (fun y => jY y=true) d τ lam)
    (B₂ : BipartiteBlockBounds EA (fun a => ¬(incoming a).isRight=true) (fun y => ¬jY y=true) d τ lam)
    (B₃ : BipartiteBlockBounds EB (fun x => (outgoing x).isRight=true) (fun y => ¬jY y=true) d τ lam)
    (B₄ : BipartiteBlockBounds EB (fun x => ¬(outgoing x).isRight=true) (fun y => ¬jY y=true) d τ lam)
    (B₅ : BipartiteBlockBounds EB (fun x => ¬(outgoing x).isRight=true) (fun y => jY y=true) d τ lam)
    (hbudget : ((Fᶜ).card:ℝ)+(N*(l+4):ℕ)/(K:ℝ)+(l+5)*(2*b+1)+8*(K+2*M:ℕ)<c) :
    ∃ C : Fin N → MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ i j, i≠j → Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))) ∧
      (∀ a, ∃ i, Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming a))∈markedWheelPhysicalResources (C i)) ∧
      (∀ x, ∃ i, Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing x))∈markedWheelPhysicalResources (C i)) ∧
      (∀ y, ∃ i, Sum.inr (v,hub y)∈markedWheelPhysicalResources (C i)) ∧
      (∀ x, (spanningRestriction (markedFamilyRim C) F).degree x≤4*(K+2*M)) ∧
      (∀ x∈F, (Finset.univ.filter (markedFamilySpokes C x)).card≤K+2*M) ∧
      (∀ w, (Finset.univ.filter (fun x => markedFamilySpokes C x w)).card≤l+4) ∧
      (∀ i, markedWheelRows (C i)⊆insert v F) ∧
      (∀ i, ∃ y, (C i).2.val=hub y) ∧
      (∀ i,v∈markedWheelRows (C i)) := by
  let labelIn := fun a => Sum.elim tail ktail (incoming a)
  let labelOut := fun x => Sum.elim head khead (outgoing x)
  obtain ⟨f,g,hf,hg,hftype,hgtype,hapart⟩ := marked_typed_endpoint_pairing_of_bounds EA EB
    (fun a => (incoming a).isRight=true) (fun x => (outgoing x).isRight=true) (fun y => jY y=true)
    (hA.trans hY.symm) (hB.trans hY.symm) (by convert hclass using 1 <;> congr!) hallowed π b M labelIn labelOut
    (by intro x; convert hlabelIn x using 1 <;> congr!)
    (by intro x; convert hlabelOut x using 1 <;> congr!)
    d τ lam hτ hlam hdegree hmargin (by convert hgap using 1 <;> congr!) B₁ B₂ B₃ B₄ B₅
  let eY : Fin N ≃ Y := Fintype.equivOfCardEq (by simpa using hY.symm)
  let ein : Fin N ≃ A := eY.trans f.symm
  let eout : Fin N ≃ B := eY.trans g.symm
  let a := labelOut ∘ eout
  let z := labelIn ∘ ein
  let u : Fin N → U := hub ∘ eY
  let ji : Fin N → Bool := fun i => (incoming (ein i)).isRight
  let jo : Fin N → Bool := fun i => (outgoing (eout i)).isRight
  have hji (i : Fin N) : ji i=jY (eY i) := by
    have hh := hftype (f.symm (eY i))
    rw [f.apply_symm_apply] at hh
    exact Bool.eq_iff_iff.mpr hh.symm
  have hjtypes (i : Fin N) : ¬(ji i=true ∧ jo i=true) := by
    rintro ⟨hi,ho⟩
    have hh := hgtype (eout i) ho
    apply hh
    simpa only [eout,Equiv.trans_apply,g.apply_symm_apply,←hji] using hi
  have hroot' (i : Fin N) : if ji i then HK v (u i) else H₀ v (u i) := by
    rw [hji]; exact hSpoke (eY i)
  have ho' (i : Fin N) : markedArcPresent tail head ktail khead (jo i) v (a i) := by
    simpa only [a,jo,labelOut,Function.comp_apply,hout] using markedArcPresent_of_edge tail head ktail khead (outgoing (eout i))
  have hi' (i : Fin N) : markedArcPresent tail head ktail khead (ji i) (z i) v := by
    simpa only [z,ji,labelIn,Function.comp_apply,hin] using markedArcPresent_of_edge tail head ktail khead (incoming (ein i))
  have hspout (i : Fin N) : if jo i then HK (a i) (u i) else H₀ (a i) (u i) := by
    have hh := hEB (eout i) (g (eout i)) (hg (eout i))
    simpa only [a,jo,u,labelOut,Function.comp_apply,eout,Equiv.trans_apply,g.apply_symm_apply] using hh
  have hspin (i : Fin N) : H₀ (z i) (u i) := by
    have hh := hEA (ein i) (f (ein i)) (hf (ein i))
    simpa only [z,u,labelIn,Function.comp_apply,ein,Equiv.trans_apply,f.apply_symm_apply] using hh
  have hrootpairs := marked_assigned_root_rims_disjoint tail head ktail khead π hphys v
    (incoming ∘ ein) (outgoing ∘ eout) (incoming.injective.comp ein.injective) (outgoing.injective.comp eout.injective)
    (fun i => hin (ein i)) (fun i => hout (eout i))
    (fun i h => hsepIn (ein i) (Or.inl h))
  have hend : ∀ x, (Finset.univ.filter (fun i => x=a i ∨ x=z i)).card≤2*M := by
    intro x
    have hh := paired_label_occurrence_bound labelOut labelIn eout ein M
      (by intro x; convert hlabelOut x using 1 <;> congr!)
      (by intro x; convert hlabelIn x using 1 <;> congr!) x
    convert hh using 1 <;> congr!
  obtain ⟨C,hC,hdis,hfree,hR,hS,hU⟩ := marked_assigned_row_packing Q hl hb F hF v hv N K (2*M) hK
    a z u ji jo (hub.injective.comp eY.injective) (fun i => hFout (eout i)) (fun i => hFin (ein i)) hjtypes
    (fun i h => hapart (eY i) ((permutationClose_symm π b _ _).mp h))
    (fun i => hsepOut (eout i)) (fun i => hsepIn (ein i)) hspout hspin hroot' ho' hi' hrootpairs hend hbudget
  have hcov (i : Fin N) :
      Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming (ein i)))∈markedWheelPhysicalResources (C i) ∧
      Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing (eout i)))∈markedWheelPhysicalResources (C i) ∧
      Sum.inr (v,u i)∈markedWheelPhysicalResources (C i) := by
    obtain ⟨hCu,p,hp0,hplast,hcoord,hpF⟩ := hC i
    have hh := marked_assigned_row_root_resources (by omega : 2≤l+2) p v (ji i) (jo i) (hjtypes i) (C i) hcoord
    rw [hp0,hplast,hCu] at hh
    have hpi : markedPhysicalEdge tail head ktail khead π (incoming (ein i))=
        if ji i then {z i,π v} else {z i,v} := by
      rw [markedPhysicalEdge_typed_formula,hin]; rfl
    have hpo : markedPhysicalEdge tail head ktail khead π (outgoing (eout i))=
        if jo i then {v,π (a i)} else {v,a i} := by
      rw [markedPhysicalEdge_typed_formula,hout]; rfl
    rw [hpi,hpo]
    exact ⟨hh.2.1,hh.1,hh.2.2⟩
  refine ⟨C,hdis,?_,?_,?_,hR,hS,hU,?_,?_,?_⟩
  · intro a
    exact ⟨ein.symm a,by simpa only [ein.apply_symm_apply] using (hcov (ein.symm a)).1⟩
  · intro x
    exact ⟨eout.symm x,by simpa only [eout.apply_symm_apply] using (hcov (eout.symm x)).2.1⟩
  · intro y
    exact ⟨eY.symm y,by simpa only [u,Function.comp_apply,eY.apply_symm_apply] using (hcov (eY.symm y)).2.2⟩

  · intro i
    obtain ⟨hCu,p,hp0,hplast,hcoord,hpF⟩ := hC i
    rw [marked_one_root_rows p v _ (C i) hcoord]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact Finset.mem_insert_self _ _
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_insert_of_mem (hpF j)
  · intro i
    exact ⟨eY i,(hC i).1⟩

  · intro i
    exact ((markedWheelPhysicalResources_spoke (C i) v (u i)).mp (hcov i).2.2).2

end Oberwolfach
