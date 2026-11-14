module

public import Oberwolfach.MarkedCycleFreshHub
public import Oberwolfach.FiniteDisjointChoices

@[expose] public section

/-! Choose all hub labels for an already constructed family of cycles.
Their ordinary and marked row prescriptions are retained exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_cycle_family_fresh_hubs
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (C:I→MarkedCycleTuple tail head ktail khead (l+4) π b) (B:Finset U)
    (hB:(B.card:ℝ)+Fintype.card I<ch):
    ∃ h:I↪U,(∀ i,h i∉B)∧∀ i,MarkedHubCompatible H₀ HK (C i).val (h i):=by
  have hc:∀ i:I,∀ T:Finset U,T.card≤B.card+Fintype.card I*1→
      ∃ u,MarkedHubCompatible H₀ HK (C i).val u∧({u}:Finset U).card≤1∧Disjoint ({u}:Finset U) T:=by
    intro i T hT
    have ht:(T.card:ℝ)≤B.card+Fintype.card I:=by exact_mod_cast (by simpa using hT)
    obtain ⟨u,hu,hCu⟩:=marked_cycle_fresh_hub Q (C i) T (ht.trans_lt hB)
    exact ⟨u,hCu,by simp,by simpa using hu⟩
  obtain ⟨h,hh,hd⟩:=finite_disjoint_choices (fun u:U=>({u}:Finset U))
    (fun i u=>MarkedHubCompatible H₀ HK (C i).val u) B 1 hc
  have hi:Function.Injective h:=by
    intro i j he
    by_contra hij
    exact Finset.disjoint_left.mp (hd i j hij) (Finset.mem_singleton_self _) (by simp [he])
  exact ⟨⟨h,hi⟩,fun i=>by simpa using (hh i).2.2,fun i=>(hh i).1⟩

end Oberwolfach
