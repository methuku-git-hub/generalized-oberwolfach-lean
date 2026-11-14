module

public import Oberwolfach.MarkedHostRimEncoding
public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section

/-! Encoding a modified typed host keeps every original interval coordinate.
On a protected inner row set the original physical coordinates can also be
kept exactly. The operation makes no assertion about a new probability law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z E K Γ Color : Type}
    [Fintype V] [Fintype W] [Fintype U] [Fintype Z] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

def rawMarkedEncodeHost (tail head:E → V) (ktail khead:K → V) (π:Equiv.Perm V)
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) : RawMarkedOutcome V U Γ Color
  | Sum.inl e=>if e.toFinset⊆I then σ (Sum.inl e) else markedHostRimEncoding tail head ktail khead π e
  | Sum.inr e=>σ (Sum.inr e)

theorem rawMarkedEncodeHost_spokes
    (tail head:E → V) (ktail khead:K → V) (π:Equiv.Perm V)
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (d:ℕ)
    (g:Γ) (j:Color) (mark:Bool) (v:V) (u:U) :
    rawMarkedPairSpokes π d (rawMarkedEncodeHost tail head ktail khead π σ I) g j mark v u ↔
      rawMarkedPairSpokes π d σ g j mark v u := Iff.rfl

theorem rawMarkedEncodeHost_inner_coordinates
    (tail head:E → V) (ktail khead:K → V) (π:Equiv.Perm V)
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (e:Sym2 V) (he:e.toFinset⊆I) :
    rawMarkedEncodeHost tail head ktail khead π σ I (Sum.inl e)=σ (Sum.inl e) := by
  simp only [rawMarkedEncodeHost,ite_eq_left he]

theorem rawMarkedEncodeHost_restrict
    (tail head:E → V) (ktail khead:K → V) (π:Equiv.Perm V)
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V)
    (f:W → V) (g:Z → U) (hf:∀ w,f w∈I) :
    rawMarkedRestrictPair f g (rawMarkedEncodeHost tail head ktail khead π σ I)=
      rawMarkedRestrictPair f g σ := by
  funext c
  cases c with
  | inl e=>
    induction e using Sym2.ind with
    | _ x y=>
      change (if s(f x,f y).toFinset⊆I then σ (Sum.inl s(f x,f y)) else _) = _
      rw [ite_eq_left (by simpa only [Sym2.toFinset_mk_eq,Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro (hf x) (hf y))]
      rfl
  | inr e=>rfl

theorem rawMarkedEncodeHost_rims
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e)))
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (hI:∀ v,π v∈I↔v∈I)
    (hAgree:∀ mark x y,x∈I → y∈I →
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y)))
    (mark:Bool) (x y:V) :
    markedPhysicalRim P π (3*d) (fun e=>rawMarkedEncodeHost tail head ktail khead π σ I (Sum.inl e)) mark x y=1 ↔
      (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y) := by
  have hm : s(x,if mark then π y else y).toFinset⊆I ↔ x∈I∧y∈I := by
    rw [Sym2.toFinset_mk_eq,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    cases mark <;> simp only [Bool.false_eq_true,↓reduceIte,hI]
  by_cases hin:x∈I∧y∈I
  · rw [markedPhysicalRim_eq_one_iff]
    have hh:=hAgree mark x y hin.1 hin.2
    rw [markedPhysicalRim_eq_one_iff] at hh
    simpa only [rawMarkedEncodeHost,ite_eq_left (hm.mpr hin)] using hh
  · rw [markedPhysicalRim_eq_one_iff]
    have hh:=markedHostRimEncoding_arcs P π (3*d) tail head ktail khead hp hE hK mark x y
    rw [markedPhysicalRim_eq_one_iff] at hh
    simpa only [rawMarkedEncodeHost,ite_eq_right (fun hh=>hin (hm.mp hh))] using hh

end Oberwolfach
