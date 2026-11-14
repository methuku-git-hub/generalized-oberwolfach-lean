module

public import Oberwolfach.MarkedFiniteDomainBalanceEmbedding
public import Oberwolfach.MarkedFiniteInducedDomainBalance
public import Oberwolfach.MarkedFiniteFullBalanceBridge

@[expose] public section

/-! The four numerical inputs of the induced inner correction follow
from the fixed-domain balances at inner roots. All occurrence identifiers
are transported explicitly, including the marked in-degree term. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteDomainBalance_univ
    (tail head : E→V) (ktail khead : K→V) (HK : V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (m : ℕ) (z : V⊕U) (i : Fin 4) :
    markedFiniteDomainBalance tail head ktail khead HK A S m Finset.univ Finset.univ z i=
      markedFiniteBalance tail head ktail khead HK A S m z i := by
  cases z with
  | inl v => simp only [markedFiniteDomainBalance,Finset.mem_univ,Finset.filter_true]
  | inr u => simp only [markedFiniteDomainBalance,Finset.mem_univ,Finset.filter_true,markedFiniteBalance]

theorem marked_induced_full_balance_eq
    (tail head : E→V) (ktail khead : K→V) (H₀ HK : V→U→Prop) (I : Finset V) (J : Finset U) (m : ℕ) :
    let EI := {e:E // tail e∈I∧head e∈I}
    let KI := {e:K // ktail e∈I∧khead e∈I}
    let tI := fun e:EI=>(⟨tail e.val,e.property.1⟩:I)
    let hI := fun e:EI=>(⟨head e.val,e.property.2⟩:I)
    let ktI := fun e:KI=>(⟨ktail e.val,e.property.1⟩:I)
    let khI := fun e:KI=>(⟨khead e.val,e.property.2⟩:I)
    let H0I := fun v:I=>fun u:J=>H₀ v.val u.val
    let HKI := fun v:I=>fun u:J=>HK v.val u.val;
    ∀ (z:I⊕J) (i:Fin 4),
    markedFiniteBalance tI hI ktI khI HKI Finset.univ
      (Finset.univ.filter (fun s:I×J=>H0I s.1 s.2∨HKI s.1 s.2)) m z i=
    markedFiniteDomainBalance tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) m I J
      (Sum.map Subtype.val Subtype.val z) i := by
  intro EI KI tI hI ktI khI H0I HKI z i
  let f:I↪V := ⟨Subtype.val,Subtype.val_injective⟩
  let g:J↪U := ⟨Subtype.val,Subtype.val_injective⟩
  let e:EI↪E := ⟨Subtype.val,Subtype.val_injective⟩
  let k:KI↪K := ⟨Subtype.val,Subtype.val_injective⟩
  let S := Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)
  let SI := Finset.univ.filter (fun s:I×J=>H0I s.1 s.2∨HKI s.1 s.2)
  have hA : Finset.univ.image (e.sumMap k)=
      Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I) := by
    ext a
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_filter]
    constructor
    · rintro ⟨b,rfl⟩
      cases b with
      | inl a => exact a.property
      | inr a => exact a.property
    · intro ha
      cases a with
      | inl a => exact ⟨Sum.inl ⟨a,ha⟩,rfl⟩
      | inr a => exact ⟨Sum.inr ⟨a,ha⟩,rfl⟩
  have hS : SI.image (Prod.map f g)=S.filter (fun s=>s.1∈I∧s.2∈J) := by
    ext s
    constructor
    · intro hs
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩,
        a.1.property,a.2.property⟩
    · intro hs
      obtain ⟨hs,hI,hJ⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_image.mpr ⟨(⟨s.1,hI⟩,⟨s.2,hJ⟩),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hs).2⟩,rfl⟩
  have hh := markedFiniteDomainBalance_embedding tI hI ktI khI tail head ktail khead HKI HK
    f g e k (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    Finset.univ SI m (fun _ _=>Iff.rfl) Finset.univ Finset.univ I J
    (fun x=>by simp only [Finset.mem_univ,iff_true];exact x.property)
    (fun u=>by simp only [Finset.mem_univ,iff_true];exact u.property) z i
  rw [hA,hS,markedFiniteDomainBalance_univ] at hh
  rw [←hh]
  apply markedFiniteDomainBalance_induced_inside tail head ktail khead HK Finset.univ S m I I J J
    (Finset.Subset.refl _) (Finset.Subset.refl _)
  cases z with
  | inl v => exact v.property
  | inr u => exact u.property

theorem marked_induced_balance_inputs
    (tail head : E→V) (ktail khead : K→V) (H₀ HK : V→U→Prop)
    (hd : ∀ v u,¬(H₀ v u∧HK v u)) (I : Finset V) (J : Finset U) (m : ℕ) (err : ℝ)
    (hbal : ∀ z,Sum.elim (fun v=>v∈I) (fun u=>u∈J) z→∀ i,
      |markedFiniteDomainBalance tail head ktail khead HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) m I J z i|≤err) :
    let EI := {e:E // tail e∈I∧head e∈I}
    let KI := {e:K // ktail e∈I∧khead e∈I}
    let tI := fun e:EI=>(⟨tail e.val,e.property.1⟩:I)
    let hI := fun e:EI=>(⟨head e.val,e.property.2⟩:I)
    let ktI := fun e:KI=>(⟨ktail e.val,e.property.1⟩:I)
    let khI := fun e:KI=>(⟨khead e.val,e.property.2⟩:I)
    let H0I := fun v:I=>fun u:J=>H₀ v.val u.val
    let HKI := fun v:I=>fun u:J=>HK v.val u.val;
    (∀ v,|occurrenceDegree (Sum.elim tI ktI) v-
      (∑ u,if H0I v u then (1:ℝ) else 0)-(∑ u,if HKI v u then (1:ℝ) else 0)|≤err) ∧
    (∀ v,|occurrenceDegree (Sum.elim hI khI) v-
      (∑ u,if H0I v u then (1:ℝ) else 0)-(∑ u,if HKI v u then (1:ℝ) else 0)|≤err) ∧
    (∀ v,|occurrenceDegree khI v-(∑ u,if HKI v u then (1:ℝ) else 0)|≤err) ∧
    (∀ u,|(∑ v,if H0I v u then (1:ℝ) else 0)-(m:ℝ)*(∑ v,if HKI v u then (1:ℝ) else 0)|≤err) := by
  intro EI KI tI hI ktI khI H0I HKI
  have hdI : ∀ v u,¬(H0I v u∧HKI v u) := fun v u=>hd v.val u.val
  have hb (z:I⊕J) (i:Fin 4) : |markedFiniteBalance tI hI ktI khI HKI Finset.univ
      (Finset.univ.filter (fun s:I×J=>H0I s.1 s.2∨HKI s.1 s.2)) m z i|≤err := by
    rw [marked_induced_full_balance_eq tail head ktail khead H₀ HK I J m]
    apply hbal
    cases z with
    | inl v => exact v.property
    | inr u => exact u.property
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    have h := hb (Sum.inl v) ((0:Fin 3).castSucc)
    rw [markedFiniteBalance_full_row tI hI ktI khI H0I HKI hdI m v (0:Fin 3)] at h
    have hi : ((0:Fin 3).castSucc:Fin 4)=(0:Fin 4) := by decide
    rw [hi,(markedSixDegreeBalance_row tI hI ktI khI H0I HKI m v).1] at h
    exact h
  · intro v
    have h := hb (Sum.inl v) ((1:Fin 3).castSucc)
    rw [markedFiniteBalance_full_row tI hI ktI khI H0I HKI hdI m v (1:Fin 3)] at h
    have hi : ((1:Fin 3).castSucc:Fin 4)=(1:Fin 4) := by decide
    rw [hi,(markedSixDegreeBalance_row tI hI ktI khI H0I HKI m v).2.1] at h
    exact h
  · intro v
    have h := hb (Sum.inl v) ((2:Fin 3).castSucc)
    rw [markedFiniteBalance_full_row tI hI ktI khI H0I HKI hdI m v (2:Fin 3)] at h
    have hi : ((2:Fin 3).castSucc:Fin 4)=(2:Fin 4) := by decide
    rw [hi,(markedSixDegreeBalance_row tI hI ktI khI H0I HKI m v).2.2] at h
    exact h
  · intro u
    have h := hb (Sum.inr u) 3
    rw [markedFiniteBalance_full_hub tI hI ktI khI H0I HKI hdI m u,
      markedSixDegreeBalance_hub] at h
    exact h

end Oberwolfach
