module

public import Oberwolfach.AvoidPartialMatching

@[expose] public section

/-! Assign each rim-incidence hub to a different attachment. The marked
incidences are sent to outgoing attachments first; all remaining incidences
are then assigned bijectively. This makes the exceptional degree pair
(1,1), and the need to pad it, explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem marked_transformer_attachment_assignment {X Y:Type*}
    [Fintype X] [Fintype Y]
    (own:X≃Y) (K:Finset X) (A:Finset Y)
    (hKA:K.card≤A.card) (hA:2≤A.card ∨ K.card=0)
    (hrem:2≤Fintype.card X-K.card):
    ∃ σ:X≃Y,(∀ x,σ x≠own x)∧∀ x∈K,σ x∈A:=by
  classical
  let Bad:K→A→Prop:=fun x y=>own x.val=y.val
  have hrow (x:K):(Finset.univ.filter (Bad x)).card≤1:=by
    apply Finset.card_le_one.mpr
    intro y hy z hz
    apply Subtype.ext
    exact (Finset.mem_filter.mp hy).2.symm.trans (Finset.mem_filter.mp hz).2
  have hcol (y:A):(Finset.univ.filter (fun x=>Bad x y)).card≤1:=by
    apply Finset.card_le_one.mpr
    intro x hx z hz
    apply Subtype.ext
    exact own.injective ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hz).2.symm)
  obtain ⟨fK,hfK⟩:=injection_avoiding_partial_matching Bad hrow hcol
    (by simpa using hKA) (by simpa using hA)
  let g:K→Y:=fun x=>(fK x).val
  have hg:Function.Injective g:=fun x y h=>fK.injective (Subtype.ext h)
  let T:Finset Y:=Finset.univ.image g
  have hT:T.card=K.card:=by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ hg,Finset.card_univ,Fintype.card_coe]
  let Xr:=((Finset.univ:Finset X)\K)
  let Yr:=((Finset.univ:Finset Y)\T)
  have hXr:Fintype.card Xr=Fintype.card X-K.card:=by
    simp only [Xr,Fintype.card_coe,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
  have hYr:Fintype.card Yr=Fintype.card Y-K.card:=by
    simp only [Yr,Fintype.card_coe,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,hT]
  let BadR:Xr→Yr→Prop:=fun x y=>own x.val=y.val
  have hrowR (x:Xr):(Finset.univ.filter (BadR x)).card≤1:=by
    apply Finset.card_le_one.mpr
    intro y hy z hz
    apply Subtype.ext
    exact (Finset.mem_filter.mp hy).2.symm.trans (Finset.mem_filter.mp hz).2
  have hcolR (y:Yr):(Finset.univ.filter (fun x=>BadR x y)).card≤1:=by
    apply Finset.card_le_one.mpr
    intro x hx z hz
    apply Subtype.ext
    exact own.injective ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hz).2.symm)
  have hcard:Fintype.card X=Fintype.card Y:=Fintype.card_congr own
  obtain ⟨fR,hfR⟩:=bijection_avoiding_partial_matching BadR hrowR hcolR
    (by rw [hXr,hYr,hcard]) (by rw [hYr,← hcard];omega)
  let f:X→Y:=fun x=>if hx:x∈K then g ⟨x,hx⟩ else
    (fR ⟨x,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hx⟩⟩).val
  have hgin (x:K):g x∈T:=Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  have hRout (x:Xr):(fR x).val∉T:=(Finset.mem_sdiff.mp (fR x).property).2
  have hf:Function.Injective f:=by
    intro x y h
    by_cases hx:x∈K <;> by_cases hy:y∈K
    · simp only [f,dite_eq_left hx,dite_eq_left hy] at h
      exact congrArg Subtype.val (hg h)
    · simp only [f,dite_eq_left hx,dite_eq_right hy] at h
      exact (hRout ⟨y,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hy⟩⟩ (h ▸ hgin ⟨x,hx⟩)).elim
    · simp only [f,dite_eq_right hx,dite_eq_left hy] at h
      exact (hRout ⟨x,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hx⟩⟩ (h.symm ▸ hgin ⟨y,hy⟩)).elim
    · simp only [f,dite_eq_right hx,dite_eq_right hy] at h
      exact congrArg Subtype.val (fR.injective (Subtype.ext h))
  let σ:X≃Y:=Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩)
  refine ⟨σ,?_,?_⟩
  · intro x
    change f x≠own x
    by_cases hx:x∈K
    · simp only [f,dite_eq_left hx]
      exact Ne.symm (hfK ⟨x,hx⟩)
    · simp only [f,dite_eq_right hx]
      exact Ne.symm (hfR ⟨x,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hx⟩⟩)
  · intro x hx
    change f x∈A
    simpa only [f,dite_eq_left hx,g] using (fK ⟨x,hx⟩).property

 theorem marked_transformer_assignment_margins (s k:ℕ) (hk:k≤s)
    (hs:0<s) (hpad:¬(s=1∧k=1)):
    (2≤s∨k=0)∧2≤2*s-k:=by omega

end Oberwolfach
