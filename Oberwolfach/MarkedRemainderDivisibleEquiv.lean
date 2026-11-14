module

public import Oberwolfach.MarkedFiniteRemainderTransfer

@[expose] public section
/-! Divisibility is invariant under bijective renaming of typed arc occurrences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_remainder_divisible_equiv
    {V U E K E' K':Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype E'] [Fintype K'] [DecidableEq V] [DecidableEq U]
    [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']
    (tail head:E→V) (ktail khead:K→V) (tail' head':E'→V) (ktail' khead':K'→V)
    (e:E≃E') (k:K≃K')
    (he₁:∀a,tail' (e a)=tail a) (he₂:∀a,head' (e a)=head a)
    (hk₁:∀a,ktail' (k a)=ktail a) (hk₂:∀a,khead' (k a)=khead a)
    (HK:V→U→Prop) (S:Finset (V×U)) (m:ℕ)
    (h:MarkedRemainderDivisible tail head ktail khead HK Finset.univ S m):
    MarkedRemainderDivisible tail' head' ktail' khead' HK Finset.univ S m:=by
  let f:↥(Finset.univ:Finset (E⊕K))→E'⊕K':=fun a=>Sum.map e k a.val
  have hf:Function.Injective f:=(Sum.map_injective.mpr ⟨e.injective,k.injective⟩).comp Subtype.val_injective
  have hs:∀a,Sum.elim tail' ktail' (f a)=Sum.elim tail ktail a.val:=by
    rintro ⟨a,ha⟩;cases a with
    | inl x=>exact he₁ x
    | inr x=>exact hk₁ x
  have hd:∀a,Sum.elim head' khead' (f a)=Sum.elim head khead a.val:=by
    rintro ⟨a,ha⟩;cases a with
    | inl x=>exact he₂ x
    | inr x=>exact hk₂ x
  have ht:∀a,markedArcType (f a)=markedArcType a.val:=by
    rintro ⟨a,ha⟩;cases a <;> rfl
  have hi:Finset.univ.image f=Finset.univ:=by
    ext a
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    cases a with
    | inl a=>exact ⟨⟨Sum.inl (e.symm a),Finset.mem_univ _⟩,by simp [f]⟩
    | inr a=>exact ⟨⟨Sum.inr (k.symm a),Finset.mem_univ _⟩,by simp [f]⟩
  have hh:=marked_finite_remainder_image_divisible (tail':=tail') (head':=head') (ktail':=ktail') (khead':=khead')
    Finset.univ S f hf hs hd ht (fun _ _=>Iff.rfl) h
  rwa [hi] at hh
end Oberwolfach
