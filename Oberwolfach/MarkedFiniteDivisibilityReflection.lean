module

public import Oberwolfach.MarkedFiniteBalanceEmbedding

@[expose] public section

/-! Exact reflection of the four divisibility identities under injective
row, hub and typed-occurrence maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K' : Type}
    [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']
    [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']

theorem marked_finite_divisibility_reflects
    (tail head : E→V) (ktail khead : K→V) (tail' head' : E'→V') (ktail' khead' : K'→V')
    (HK : V→U→Prop) (HK' : V'→U'→Prop) (f : V↪V') (g : U↪U') (e : E↪E') (k : K↪K')
    (ht : ∀ a,tail' (e a)=f (tail a)) (hh : ∀ a,head' (e a)=f (head a))
    (hkt : ∀ a,ktail' (k a)=f (ktail a)) (hkh : ∀ a,khead' (k a)=f (khead a))
    (A : Finset (E⊕K)) (S : Finset (V×U)) (m : ℕ)
    (hHK : ∀ z∈S,HK' (f z.1) (g z.2)↔HK z.1 z.2)
    (hdiv : MarkedRemainderDivisible tail' head' ktail' khead' HK'
      (A.image (e.sumMap k)) (S.image (Prod.map f g)) m) :
    MarkedRemainderDivisible tail head ktail khead HK A S m := by
  apply (markedFiniteBalance_eq_zero_iff tail head ktail khead HK A S m).mp
  intro z i
  rw [←markedFiniteBalance_embedding tail head ktail khead tail' head' ktail' khead' HK HK'
    f g e k ht hh hkt hkh A S m hHK z i]
  exact (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mpr hdiv _ _

end Oberwolfach
