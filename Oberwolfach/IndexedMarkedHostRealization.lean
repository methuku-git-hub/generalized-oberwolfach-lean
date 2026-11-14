module

public import Oberwolfach.IndexedMarkedRootPair
public import Oberwolfach.MarkedPresentOccurrenceInjection

@[expose] public section

/-! A displayed realisation of an indexed marked graph in the original
host. The vertex maps may identify vertices, but edge occurrences do not. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
variable {V₀ U₀ V U E K A S:Type} [DecidableEq V]

structure IndexedMarkedHostRealization (G:IndexedMarkedGraph V₀ U₀ A S)
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b:ℕ) where
  rows:V₀→V
  hubs:U₀→U
  rimPresent:∀ a,markedArcPresent tail head ktail khead (G.jr a) (rows (G.src a)) (rows (G.dst a))
  spokePresent:∀ s,if G.js s then HK (rows (G.row s)) (hubs (G.hub s)) else H₀ (rows (G.row s)) (hubs (G.hub s))
  arcSeparated:∀ a,¬PermutationClose π b (rows (G.src a)) (rows (G.dst a))
  rimInjective:Function.Injective (fun a=>if G.jr a then
    ({rows (G.src a),π (rows (G.dst a))}:Finset V) else {rows (G.src a),rows (G.dst a)})
  spokeInjective:Function.Injective (fun s=>(rows (G.row s),hubs (G.hub s)))

def IndexedMarkedHostRealization.resources [Fintype A] [Fintype S] [DecidableEq U]
    {G:IndexedMarkedGraph V₀ U₀ A S}
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b:ℕ}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b):Finset (Finset V⊕(V×U)):=
  markedRootGraphResources π (R.rows∘G.src) (R.rows∘G.dst) (R.rows∘G.row) G.jr (R.hubs∘G.hub)

end Oberwolfach
