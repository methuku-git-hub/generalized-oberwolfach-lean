module

public import Oberwolfach.RawMarkedResourceCoordinates

@[expose] public section

/-! A physically injective typed host can be represented by categorical
rim coordinates. This is deterministic encoding of a given host, not a
claim that it has the distribution of a fresh random sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K : Type} [LinearOrder V]

def markedHostPhysicalCoordinate (tail head:E → V) (ktail khead:K → V) (π:Equiv.Perm V) : E⊕K → Sym2 V :=
  Sum.elim (fun e=>s(tail e,head e)) (fun e=>s(ktail e,π (khead e)))

theorem markedHostPhysicalCoordinate_injective
    (tail head:E → V) (ktail khead:K → V) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)) :
    Function.Injective (markedHostPhysicalCoordinate tail head ktail khead π) := by
  intro a b hab
  apply hp
  have hh:=congrArg Sym2.toFinset hab
  cases a <;> cases b <;>
    simpa only [markedHostPhysicalCoordinate,Sum.elim_inl,Sum.elim_inr,Sym2.toFinset_mk_eq,markedPhysicalEdge] using hh

def markedHostRimState (tail head:E → V) (ktail khead:K → V) (π:Equiv.Perm V) : E⊕K → Bool×Bool :=
  Sum.elim (fun e=>(false,orientationBit (tail e) (head e)))
    (fun e=>(true,orientationBit (ktail e) (π (khead e))))

def markedHostRimEncoding (tail head:E → V) (ktail khead:K → V) (π:Equiv.Perm V)
    (e:Sym2 V) : Option (Bool×Bool) :=
  if h:∃ a:E⊕K,markedHostPhysicalCoordinate tail head ktail khead π a=e then
    some (markedHostRimState tail head ktail khead π (Classical.choose h)) else none

theorem markedHostRimEncoding_at
    (tail head:E → V) (ktail khead:K → V) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)) (a:E⊕K) :
    markedHostRimEncoding tail head ktail khead π (markedHostPhysicalCoordinate tail head ktail khead π a)=
      some (markedHostRimState tail head ktail khead π a) := by
  have hh:∃ b,markedHostPhysicalCoordinate tail head ktail khead π b=
      markedHostPhysicalCoordinate tail head ktail khead π a:=⟨a,rfl⟩
  rw [markedHostRimEncoding,dite_eq_left hh]
  rw [markedHostPhysicalCoordinate_injective tail head ktail khead π hp (Classical.choose_spec hh)]

theorem markedHostRimEncoding_exists_of_some
    (tail head:E → V) (ktail khead:K → V) (π:Equiv.Perm V)
    (e:Sym2 V) (state:Bool×Bool)
    (he:markedHostRimEncoding tail head ktail khead π e=some state) :
    ∃ a,markedHostPhysicalCoordinate tail head ktail khead π a=e := by
  by_contra hh
  simp only [markedHostRimEncoding,dite_eq_right hh] at he
  cases he

theorem markedHostRimEncoding_arcs
    (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π b (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π b (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e)))
    (mark:Bool) (x y:V) :
    markedPhysicalRim P π b (markedHostRimEncoding tail head ktail khead π) mark x y=1 ↔
      (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y) := by
  let σ:=markedHostRimEncoding tail head ktail khead π
  have he (e:E):markedPhysicalRim P π b σ false (tail e) (head e)=1 := by
    apply (markedPhysicalRim_eq_one_iff _ _ _ _ _ _ _).mpr
    refine ⟨(hE e).1,(hE e).2,?_⟩
    exact markedHostRimEncoding_at tail head ktail khead π hp (Sum.inl e)
  have hk (e:K):markedPhysicalRim P π b σ true (ktail e) (khead e)=1 := by
    apply (markedPhysicalRim_eq_one_iff _ _ _ _ _ _ _).mpr
    refine ⟨(hK e).1,(hK e).2,?_⟩
    exact markedHostRimEncoding_at tail head ktail khead π hp (Sum.inr e)
  constructor
  · intro h
    have hs:=(markedPhysicalRim_eq_one_iff P π b σ mark x y).mp h
    obtain ⟨a,ha⟩:=markedHostRimEncoding_exists_of_some tail head ktail khead π _ _ hs.2.2
    cases a with
    | inl a=>
      have hh:=markedPhysicalRim_physical_unique P π b σ mark false x y (tail a) (head a) h (he a) ha.symm
      cases mark
      · exact ⟨a,hh.2.1.symm,hh.2.2.symm⟩
      · cases hh.1
    | inr a=>
      have hh:=markedPhysicalRim_physical_unique P π b σ mark true x y (ktail a) (khead a) h (hk a) ha.symm
      cases mark
      · cases hh.1
      · exact ⟨a,hh.2.1.symm,hh.2.2.symm⟩
  · cases mark
    · rintro ⟨a,rfl,rfl⟩;exact he a
    · rintro ⟨a,rfl,rfl⟩;exact hk a

end Oberwolfach
