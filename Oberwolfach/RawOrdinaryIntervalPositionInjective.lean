module

public import Oberwolfach.RetainedAndRawIntervalGeometry

@[expose] public section
/-! All positions in the approximate intervals at one hub are distinct. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_ordinary_interval_position_injective
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U)
    (a b:{x:V // rawIntervalColouredStart π d (fun e=>σ (w,e)) x true})
    (j k:ℕ) (hj:j<d) (hk:k<d) (he:(π^j) a.val=(π^k) b.val):
    a=b ∧ j=k:=by
  have geom:=retained_and_raw_interval_geometry π d hd hnoshort σ false true (by decide) t J w
  let ia:retainedAndRawIntervalIndex π d σ false true t J w:=.inr a
  let ib:retainedAndRawIntervalIndex π d σ false true t J w:=.inr b
  have hrootA:retainedAndRawIntervalRoot π d σ false true t J w ia=a.val:=rfl
  have hrootB:retainedAndRawIntervalRoot π d σ false true t J w ib=b.val:=rfl
  have hmemA:(π^j) a.val∈permutationWindow π 0 d a.val:=by
    apply (permutationWindow_mem_iff π 0 d a.val _).mpr
    exact ⟨⟨j,by omega⟩,by simpa⟩
  have hmemB:(π^k) b.val∈permutationWindow π 0 d b.val:=by
    apply (permutationWindow_mem_iff π 0 d b.val _).mpr
    exact ⟨⟨k,by omega⟩,by simpa⟩
  have hab:a=b:=by
    by_contra h
    have hne:ia≠ib:=by
      intro hh
      apply h
      exact Sum.inr.inj hh
    have hdis:=geom.2 ia ib hne
    rw [hrootA,hrootB] at hdis
    exact Finset.disjoint_left.mp hdis hmemA (he ▸ hmemB)
  subst b
  have hF:(⟨j,by omega⟩:Fin (d+1))=⟨k,by omega⟩:=(geom.1 ia) (by simpa [hrootA] using he)
  exact ⟨rfl,congrArg Fin.val hF⟩
end Oberwolfach
