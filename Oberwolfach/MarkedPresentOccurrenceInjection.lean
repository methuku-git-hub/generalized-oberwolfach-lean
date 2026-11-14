module

public import Oberwolfach.MarkedRootGraphSupport
public import Oberwolfach.MarkedHostExtensionCounts

@[expose] public section

/-! Distinct ordered occurrences remain distinct physical edges whenever
they are realised in the original host with its injective physical map. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V E K A:Type} [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

theorem marked_present_occurrences_physical_injective
    [Fintype A] (src dst:A→V) (jr:A→Bool)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (ha:∀ a,markedArcPresent tail head ktail khead (jr a) (src a) (dst a))
    (hi:Function.Injective (fun a=>(src a,dst a))):
    Function.Injective (fun a=>if jr a then ({src a,π (dst a)}:Finset V) else {src a,dst a}):=by
  intro a a' he
  obtain ⟨e,hp₁,ht₁,hh₁⟩:=marked_root_rim_occurrence (π:=π) src dst jr ha a
  obtain ⟨e',hp₂,ht₂,hh₂⟩:=marked_root_rim_occurrence (π:=π) src dst jr ha a'
  have hee:e=e':=hp (hp₁.trans (he.trans hp₂.symm))
  apply hi
  apply Prod.ext
  · exact ht₁.symm.trans ((congrArg (Sum.elim tail ktail) hee).trans ht₂)
  · exact hh₁.symm.trans ((congrArg (Sum.elim head khead) hee).trans hh₂)

theorem mapped_pair_injective {V₀ U₀ U S:Type} (row:S→V₀) (hub:S→U₀)
    (f:V₀→V) (g:U₀→U) (hf:Function.Injective f) (hg:Function.Injective g)
    (hi:Function.Injective (fun s=>(row s,hub s))):
    Function.Injective (fun s=>(f (row s),g (hub s))):=by
  intro s s' he
  exact hi (Prod.ext (hf (congrArg Prod.fst he)) (hg (congrArg Prod.snd he)))

end Oberwolfach
