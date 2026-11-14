module

public import Oberwolfach.MarkedAttachedCycle
public import Oberwolfach.MarkedExclusionBudget

@[expose] public section

/-! Expand a formal spoke by constructing its private hub, crossed spoke
and marked wheel. The formal old spoke is not required to be present. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_single_spoke_fresh_hub
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (j:Bool) (v:V) (B:Finset U) (hB:(B.card:ℝ)<ch):
    ∃ u∉B,if j then HK v u else H₀ v u:=by
  have hsep:∀ x∈({v}:Finset V),∀ y∈({v}:Finset V),x≠y→¬PermutationClose π b x y:=by
    intro x hx y hy hne
    exact False.elim (hne ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm))
  have hc:ch≤((Finset.univ.filter (fun u=>if j then HK v u else H₀ v u)).card:ℝ):=by
    cases j
    · simpa using Q.hubs {v} ∅ (by simp) (by simp) (by simpa using hsep)
    · simpa using Q.hubs ∅ {v} (by simp) (by simp) (by simpa using hsep)
  have hn:B.card<(Finset.univ.filter (fun u=>if j then HK v u else H₀ v u)).card:=by exact_mod_cast hB.trans_le hc
  obtain ⟨u,hu,huB⟩:=Finset.exists_mem_notMem_of_card_lt_card hn
  exact ⟨u,huB,(Finset.mem_filter.mp hu).2⟩

theorem marked_spoke_expansion_wheel
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (j:Bool) (W Z:Finset V) (B:Finset U) (x:V) (u:U) (hx:x∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+l+16)*(2*b+1)<c) (hB:(B.card:ℝ)<ch):
    ∃ C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      C.2.val∉B∧(if j then HK x C.2.val else H₀ x C.2.val)∧
      (if j then HK (C.1.val (markedExpansionSpokePosition (l+4) (by omega) j)) u
        else H₀ (C.1.val (markedExpansionSpokePosition (l+4) (by omega) j)) u)∧
      ∀ i,C.1.val i∉W∧C.1.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.1.val i) z:=by
  obtain ⟨u',hu',hxu'⟩:=marked_single_spoke_fresh_hub Q j x B hB
  have hb0:(W.card:ℝ)+Z.card*(2*b+1)<c:=by
    have hh:=marked_exclusion_budget_mono W Z Z 0 (l+16) b c (by omega)
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
    simpa using hh
  obtain ⟨v,hv,hvW,hvZ,hvs⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun v=>markedArcPresent tail head ktail khead false x v∧markedSpokesTo H₀ HK j {u,u'} v))
    W Z (Q.outgoing false j x {u,u'} (by simpa using Finset.card_insert_le u {u'})) hb0
  have hvsp:= (markedSpokesTo_pair H₀ HK j v u u').mp (Finset.mem_filter.mp hv).2.2
  have hi:=Finset.card_insert_le v Z
  have hbc:(W.card:ℝ)+((insert v Z).card+l+12)*(2*b+1)<c:=by
    have hh:=marked_exclusion_budget_mono W Z (insert v Z) (l+12) (l+16) b c (by omega)
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
    simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hh
  obtain ⟨D,hD,hav,hDu⟩:=marked_cycle_at_typed_position Q hl j {u'} (by simp) W (insert v Z) v
    (Finset.mem_insert_self _ _) ((markedSpokesTo_singleton H₀ HK j v u').mpr hvsp.2) hbc
  let C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK:=⟨D,⟨u',hDu u' (Finset.mem_singleton_self _)⟩⟩
  refine ⟨C,hu',hxu',?_,?_⟩
  · change if j then HK (D.val _) u else H₀ (D.val _) u
    rw [hD];exact hvsp.1
  · intro i
    by_cases he:i=markedExpansionSpokePosition (l+4) (by omega) j
    · subst i;change D.val _∉W∧D.val _∉Z∧_;rw [hD];exact ⟨hvW,hvZ,hvs⟩
    · exact ⟨(hav i he).1,fun hh=>(hav i he).2.1 (Finset.mem_insert_of_mem hh),
        fun z hz=>(hav i he).2.2 z (Finset.mem_insert_of_mem hz)⟩

end Oberwolfach
