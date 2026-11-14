module

public import Oberwolfach.MarkedOutsideBalanceArcPullback
public import Oberwolfach.MarkedOutsideBalanceVertexPullback
public import Oberwolfach.MarkedRestrictedSampleArcRange

@[expose] public section

/-! Restrict a cleared marked host to its actual remaining vertex and hub
domains. Support hypotheses ensure that every surviving occurrence and
spoke is represented, so the exact outside balance equations are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A U B Γ Color:Type} [Fintype V] [Fintype A] [Fintype U] [Fintype B]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq B]

theorem marked_restricted_sample_outside_balance
    (f:A↪oV) (g:B↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (X:Finset A) (Z:Finset B) (I:Finset V) (J:Finset U)
    (hX:∀ x,f x∈I↔x∈X) (hZ:∀ u,g u∈J↔u∈Z)
    (hA:∀ j,∀ e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) j,
      e.val.1∈Finset.univ.image f∧e.val.2∈Finset.univ.image f)
    (hS:∀ v u,H false v u∨H true v u→v∈Finset.univ.image f∧u∈Finset.univ.image g):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    MarkedOutsideBalance (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)) m I J→
    let σ':=rawMarkedRestrictPair f g σ
    let H':=fun b x u=>H b (f x) (g u)
    let E₀':=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ' (Sum.inl e)) true
    MarkedOutsideBalance (fun e:E₀'=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:A×B=>H' false z.1 z.2∨H' true z.1 z.2)) m X Z:=by
  intro E₀ E₁ h
  let e:=markedRestrictedSampleArcEmbedding f g π ρ hf P d σ false
  let k:=markedRestrictedSampleArcEmbedding f g π ρ hf P d σ true
  have hr (j:Bool):Finset.univ.image (markedRestrictedSampleArcEmbedding f g π ρ hf P d σ j)=Finset.univ:=by
    rw [markedRestrictedSampleArcEmbedding_range]
    exact Finset.filter_true_of_mem (fun a _=>hA j a)
  have hsurj (j:Bool):Function.Surjective (markedRestrictedSampleArcEmbedding f g π ρ hf P d σ j):=by
    intro a
    have ha:a∈Finset.univ.image (markedRestrictedSampleArcEmbedding f g π ρ hf P d σ j):=by rw [hr];exact Finset.mem_univ _
    simpa only [Finset.mem_image,Finset.mem_univ,true_and] using ha
  have hAr:Finset.univ.image (e.sumMap k)=Finset.univ:=by
    apply Finset.eq_univ_of_forall
    intro a
    cases a with
    | inl a=>
      obtain ⟨a,rfl⟩:=hsurj false a
      exact Finset.mem_image.mpr ⟨Sum.inl a,Finset.mem_univ _,rfl⟩
    | inr a=>
      obtain ⟨a,rfl⟩:=hsurj true a
      exact Finset.mem_image.mpr ⟨Sum.inr a,Finset.mem_univ _,rfl⟩
  let S:=Finset.univ.filter (fun z:A×B=>H false (f z.1) (g z.2)∨H true (f z.1) (g z.2))
  have hSr:S.image (Prod.map f g)=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2):=by
    ext z
    constructor
    · rintro hz
      obtain ⟨z,hzS,rfl⟩:=Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hzS).2⟩
    · intro hz
      have hh: H false z.1 z.2∨H true z.1 z.2:=(Finset.mem_filter.mp hz).2
      obtain ⟨ha,hb⟩:=hS z.1 z.2 hh
      obtain ⟨a,_,ha⟩:=Finset.mem_image.mp ha
      obtain ⟨b,_,hb⟩:=Finset.mem_image.mp hb
      refine Finset.mem_image.mpr ⟨(a,b),?_,Prod.ext ha hb⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [ha,hb] using hh⟩
  let E₀':=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) false
  let E₁':=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) true
  have hh:=marked_outside_balance_arc_pullback
    (fun a:E₀'=>f a.val.1) (fun a=>f a.val.2) (fun a:E₁'=>f a.val.1) (fun a=>f a.val.2)
    (fun a:E₀=>a.val.1) (fun a=>a.val.2) (fun a:E₁=>a.val.1) (fun a=>a.val.2)
    (H true) e k (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    Finset.univ (S.image (Prod.map f g)) m I J (by rw [hAr,hSr];exact h)
  exact marked_outside_balance_vertex_pullback
    (fun a:E₀'=>a.val.1) (fun a=>a.val.2) (fun a:E₁'=>a.val.1) (fun a=>a.val.2)
    (fun x u=>H true (f x) (g u)) (H true) f.toEmbedding g Finset.univ S m X Z I J
    hX hZ (fun _ _=>Iff.rfl) hh

end Oberwolfach
