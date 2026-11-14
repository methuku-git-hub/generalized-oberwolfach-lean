module

public import Oberwolfach.RetainedMarkedIntervalGeometry

@[expose] public section
/-! The same mixed outcome provides one pairwise-disjoint extended interval
family consisting of retained final intervals and raw approximate intervals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U] [DecidableEq Γ]

def retainedAndRawIntervalIndex (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U):Type:=
  retainedMarkedIndex π d σ g₀ t J w ⊕ {a:V // rawIntervalColouredStart π d (fun e=>σ (w,e)) a g₁}

instance (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U):
    Fintype (retainedAndRawIntervalIndex π d σ g₀ g₁ t J w):=by
  classical
  unfold retainedAndRawIntervalIndex retainedMarkedIndex
  infer_instance

def retainedAndRawIntervalRoot (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U):
    retainedAndRawIntervalIndex π d σ g₀ g₁ t J w→V
  | .inl a=>a.val
  | .inr a=>a.val

theorem retained_and_raw_interval_geometry
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀ g₁:Γ) (hclasses:g₀≠g₁) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t):
    ∀w,
      let root:=retainedAndRawIntervalRoot π d σ g₀ g₁ t J w
      (∀j,Function.Injective (fun i:Fin (d+1)=>(π^i.val) (root j))) ∧
      (∀j l,j≠l→Disjoint (permutationWindow π 0 d (root j)) (permutationWindow π 0 d (root l))):=by
  classical
  intro w root
  have hkeep:∀j:retainedAndRawIntervalIndex π d σ g₀ g₁ t J w,
      rawIntervalKept π d (fun x=>σ (w,Sum.inl x)) (root j):=by
    intro j
    cases j with
    | inl a=>exact a.property.1.1
    | inr a=>exact a.property.1
  have hrootinj:Function.Injective root:=by
    intro j l he
    cases j with
    | inl a =>
      cases l with
      | inl b =>
        have hh:a=b:=Subtype.ext he
        subst b
        rfl
      | inr b =>
        have h0:=a.property.1.2
        have h1:=b.property.2
        change a.val=b.val at he
        rw [he] at h0
        exact False.elim (hclasses (Option.some.inj (h0.symm.trans h1)))
    | inr a =>
      cases l with
      | inl b =>
        have h0:=b.property.1.2
        have h1:=a.property.2
        change a.val=b.val at he
        rw [←he] at h0
        exact False.elim (hclasses (Option.some.inj (h0.symm.trans h1)))
      | inr b =>
        have hh:a=b:=Subtype.ext he
        subst b
        rfl
  constructor
  · intro j
    apply permutation_short_interval_injective π (d+1) ?_ (root j)
    intro x l hl hld
    exact hnoshort x l hl (by omega)
  · intro j l hjl
    exact rawInterval_extended_disjoint π d (fun x=>σ (w,Sum.inl x)) (root j) (root l) (hkeep j) (hkeep l)
      (fun h=>hjl (hrootinj h))
end Oberwolfach
