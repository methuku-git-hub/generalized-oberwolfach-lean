module

public import Oberwolfach.OrderedCanonicalCommonPaths
public import Oberwolfach.CommonMarkedPathConstraintCounts

@[expose] public section

/-! Exact change of the free-coordinate order and the resulting deletion
estimate. The two fixed roots are unchanged and their spokes are omitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} {tail head:E→V} {ktail khead:K→V}
    {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem rootedCycleOrder_from_canonical (σ:Equiv.Perm (Fin (m+1))) (v w:V) (z:Fin m→V):
    rootedCycleOrder σ w (fun l=>Fin.insertNth (α:=fun _=>V) (σ.symm 0) v z (σ.symm l.succ))=
      Fin.insertNth (α:=fun _=>V) (σ.symm 0) w z:=by
  funext a
  by_cases ha:a=σ.symm 0
  · subst a
    simp only [rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_zero,Fin.insertNth_apply_same]
  · have hσ:σ a≠0:=by intro he;exact ha (σ.injective (by simpa using he))
    obtain ⟨l,hl⟩:=Fin.eq_succ_of_ne_zero hσ
    have he:σ.symm l.succ=a:=by rw [←hl,Equiv.symm_apply_apply]
    obtain ⟨k,hk⟩:=Fin.exists_succAbove_eq ha
    simp only [rootedCycleOrder,hl,Fin.cases_succ,he]
    rw [←hk,Fin.insertNth_apply_succAbove,Fin.insertNth_apply_succAbove]

def orderedCommonMarkedPathCanonicalEquiv (σ:Equiv.Perm (Fin (m+1))) (v v':V) (u u':U):
    OrderedCommonMarkedPath tail head ktail khead m π b H₀ Hₖ σ v v' u u'≃
      CanonicalCommonMarkedPath tail head ktail khead m π b H₀ Hₖ (σ.symm 0) v v' u u':=
  Equiv.ofBijective (orderedCommonMarkedPath_to_canonical σ v v' u u') ⟨
    (orderedCommonMarkedPath_to_canonical σ v v' u u').injective,by
      intro z
      let f:Fin m→V:=fun l=>Fin.insertNth (α:=fun _=>V) (σ.symm 0) v z.val (σ.symm l.succ)
      have hf:∀ w,rootedCycleOrder σ w f=Fin.insertNth (α:=fun _=>V) (σ.symm 0) w z.val:=
        fun w=>rootedCycleOrder_from_canonical σ v w z.val
      have hs:∀ l:Fin m,
          (if markedPositionType (σ.symm l.succ) then Hₖ (f l) u else H₀ (f l) u)∧
          (if markedPositionType (σ.symm l.succ) then Hₖ (f l) u' else H₀ (f l) u'):=by
        intro l
        have hne:σ.symm l.succ≠σ.symm 0:=fun h=>Fin.succ_ne_zero l (σ.symm.injective h)
        obtain ⟨k,hk⟩:=Fin.exists_succAbove_eq hne
        simpa only [f,←hk,Fin.insertNth_apply_succAbove] using z.property.2.2 k
      let y:OrderedCommonMarkedPath tail head ktail khead m π b H₀ Hₖ σ v v' u u':=
        ⟨f,by rw [hf];exact z.property.1,by rw [hf];exact z.property.2.1,hs⟩
      refine ⟨y,?_⟩
      apply Subtype.ext
      funext k
      change rootedCycleOrder σ v f ((σ.symm 0).succAbove k)=z.val k
      rw [hf,Fin.insertNth_apply_succAbove]⟩

def rootFirstCommonMarkedPathCanonicalEquiv (j:Bool) (v v':V) (u u':U):
    RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' u u'≃
      CanonicalCommonMarkedPath tail head ktail khead m π b H₀ Hₖ
        ((markedRootOrder m j).symm 0) v v' u u':=
  (rootFirstCommonMarkedPathEquiv j v v' u u').trans
    (orderedCommonMarkedPathCanonicalEquiv (markedRootOrder m j) v v' u u')

theorem rootFirstCommonMarkedPath_deletion_count [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (hm:1≤m) (PE:E→Prop) (PK:K→Prop) (H₀' Hₖ':V→U→Prop)
    (j:Bool) (v v':V) (u u':U) (d:ℝ)
    (hEout:∀ x,(∑ e,if ¬PE e∧tail e=x then (1:ℝ) else 0)≤d)
    (hEin:∀ x,(∑ e,if ¬PE e∧head e=x then (1:ℝ) else 0)≤d)
    (hKout:∀ x,(∑ e,if ¬PK e∧ktail e=x then (1:ℝ) else 0)≤d)
    (hKin:∀ x,(∑ e,if ¬PK e∧khead e=x then (1:ℝ) else 0)≤d)
    (hH₀:∀ u,(∑ x,if H₀ x u∧¬H₀' x u then (1:ℝ) else 0)≤d)
    (hHₖ:∀ u,(∑ x,if Hₖ x u∧¬Hₖ' x u then (1:ℝ) else 0)≤d):
    (Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' u u'):ℝ)-
      Fintype.card (RootFirstCommonMarkedPath (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ' j v v' u u')≤
      4*((m:ℝ)+1)*d*(Fintype.card V:ℝ)^(m-1):=by
  rw [Fintype.card_congr (rootFirstCommonMarkedPathCanonicalEquiv j v v' u u'),
    Fintype.card_congr (rootFirstCommonMarkedPathCanonicalEquiv j v v' u u')]
  exact commonMarkedPath_deletion_count hm tail head ktail khead π b PE PK H₀ Hₖ H₀' Hₖ'
    ((markedRootOrder m j).symm 0) v v' u u' d hEout hEin hKout hKin hH₀ hHₖ

end Oberwolfach
