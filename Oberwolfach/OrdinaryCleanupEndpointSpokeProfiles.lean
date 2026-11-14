module

public import Oberwolfach.OrdinaryCleanupAbsoluteDomainCounts

@[expose] public section
/-! The actual endpoint spoke classes retain their sampled two- and
    three-root means after the permitted symmetric edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_endpoint_spoke_profiles
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ):
    (∀x v,x≠v→¬F.Adj x v→
      |((B.filter (fun u=>H x u∧H v u)).card:ℝ)-pH^2*B.card|≤tH+2*L) ∧
    (∀x v w,x≠v→x≠w→v≠w→¬F.Adj x v→¬F.Adj x w→¬F.Adj v w→
      |((B.filter (fun u=>H x u∧H v u∧H w u)).card:ℝ)-pH^3*B.card|≤tH+3*L) := by
  have hc:=ordinary_cleanup_absolute_domain_counts P Q F H A B π d j s pR pH density tR tH L βe βh σ profile
  constructor
  · intro x v hxv hF
    have hfree:∀a∈({x,v}:Finset V),∀b∈({x,v}:Finset V),¬F.Adj a b:=by
      intro a ha b hb
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
      · exact fun h=>F.irrefl h
      · exact hF
      · exact fun h=>hF h.symm
      · exact fun h=>F.irrefl h
    have hh:=hc.2 {x,v} (by simp [hxv]) hfree
    have he:common B ({x,v}:Finset V) (fun z=>Finset.univ.filter (H z))=
        B.filter (fun u=>H x u∧H v u):=by ext u;simp [mem_common_iff]
    rw [he,Finset.card_pair hxv] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  · intro x v w hxv hxw hvw hxvF hxwF hvwF
    have hfree:∀a∈({x,v,w}:Finset V),∀b∈({x,v,w}:Finset V),¬F.Adj a b:=by
      intro a ha b hb
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl
      · exact fun h=>F.irrefl h
      · exact hxvF
      · exact hxwF
      · exact fun h=>hxvF h.symm
      · exact fun h=>F.irrefl h
      · exact hvwF
      · exact fun h=>hxwF h.symm
      · exact fun h=>hvwF h.symm
      · exact fun h=>F.irrefl h
    have hcard:({x,v,w}:Finset V).card=3:=by simp [hxv,hxw,hvw]
    have hh:=hc.2 {x,v,w} (by omega) hfree
    have he:common B ({x,v,w}:Finset V) (fun z=>Finset.univ.filter (H z))=
        B.filter (fun u=>H x u∧H v u∧H w u):=by ext u;simp [mem_common_iff]
    rw [he,hcard] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
end Oberwolfach
