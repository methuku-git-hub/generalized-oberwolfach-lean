module

public import Oberwolfach.IndexedMarkedRealizationVertexMap

@[expose] public section

/-! Restrict the abstract vertex domains to vertices incident with an
actual rim or spoke occurrence. No isolated ambient vertices are charged
to the size of the absorber input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

def IndexedMarkedGraph.activeRows (G:IndexedMarkedGraph V₀ U₀ A S):Finset V₀:=
  Finset.univ.image G.src∪Finset.univ.image G.dst∪Finset.univ.image G.row
def IndexedMarkedGraph.activeHubs (G:IndexedMarkedGraph V₀ U₀ A S):Finset U₀:=Finset.univ.image G.hub

theorem IndexedMarkedGraph.src_active (G:IndexedMarkedGraph V₀ U₀ A S) (a:A):G.src a∈G.activeRows:=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩))
theorem IndexedMarkedGraph.dst_active (G:IndexedMarkedGraph V₀ U₀ A S) (a:A):G.dst a∈G.activeRows:=
  Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩))
theorem IndexedMarkedGraph.row_active (G:IndexedMarkedGraph V₀ U₀ A S) (s:S):G.row s∈G.activeRows:=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩)
theorem IndexedMarkedGraph.hub_active (G:IndexedMarkedGraph V₀ U₀ A S) (s:S):G.hub s∈G.activeHubs:=
  Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩

def IndexedMarkedGraph.active (G:IndexedMarkedGraph V₀ U₀ A S):IndexedMarkedGraph G.activeRows G.activeHubs A S where
  src a:=⟨G.src a,G.src_active a⟩
  dst a:=⟨G.dst a,G.dst_active a⟩
  row s:=⟨G.row s,G.row_active s⟩
  hub s:=⟨G.hub s,G.hub_active s⟩
  jr:=G.jr
  js:=G.js

theorem IndexedMarkedGraph.active_map (G:IndexedMarkedGraph V₀ U₀ A S):
    G.active.map Subtype.val Subtype.val=G:=rfl

theorem IndexedMarkedGraph.active_balanced (G:IndexedMarkedGraph V₀ U₀ A S) (hG:G.IsBalanced m):
    G.active.IsBalanced m:=by
  constructor
  · intro v
    simpa only [active,Subtype.ext_iff] using hG.directed v.val
  · intro v
    simpa only [active,Subtype.ext_iff] using hG.row v.val
  · intro v
    simpa only [active,Subtype.ext_iff] using hG.marked v.val
  · intro u
    simpa only [active,Subtype.ext_iff] using hG.hub u.val

def IndexedMarkedHostRealization.active {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b):
    IndexedMarkedHostRealization G.active tail head ktail khead H₀ HK π b:=
  IndexedMarkedHostRealization.ofVertexMap G.active R Subtype.val Subtype.val G.active_map

theorem IndexedMarkedHostRealization.active_resources {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b):R.active.resources=R.resources:=
  IndexedMarkedHostRealization.resources_ofVertexMap G.active R Subtype.val Subtype.val G.active_map

theorem IndexedMarkedHostRealization.active_occurrence_bound {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (s:ℕ) (hs:G.activeRows.card+G.activeHubs.card≤s):Fintype.card A+Fintype.card S≤3*s*s:=by
  let f:A→Bool×G.activeRows×G.activeRows:=fun a=>(G.jr a,G.active.src a,G.active.dst a)
  have hf:Function.Injective f:=by
    intro a a' he
    have hj:G.jr a=G.jr a':=congrArg Prod.fst he
    have ht:G.src a=G.src a':=congrArg (fun x:Bool×G.activeRows×G.activeRows=>x.2.1.val) he
    have hh:G.dst a=G.dst a':=congrArg (fun x:Bool×G.activeRows×G.activeRows=>x.2.2.val) he
    apply R.rimInjective
    simp only [hj,ht,hh]
  let g:S→G.activeRows×G.activeHubs:=fun a=>(G.active.row a,G.active.hub a)
  have hg:Function.Injective g:=by
    intro a a' he
    have ht:G.row a=G.row a':=congrArg (fun x:G.activeRows×G.activeHubs=>x.1.val) he
    have hh:G.hub a=G.hub a':=congrArg (fun x:G.activeRows×G.activeHubs=>x.2.val) he
    apply R.spokeInjective
    simp only [ht,hh]
  have ha:Fintype.card A≤2*G.activeRows.card*G.activeRows.card:=by
    simpa only [Fintype.card_prod,Fintype.card_bool,Fintype.card_coe,Nat.mul_assoc] using Fintype.card_le_of_injective f hf
  have hh:Fintype.card S≤G.activeRows.card*G.activeHubs.card:=by
    simpa only [Fintype.card_prod,Fintype.card_coe] using Fintype.card_le_of_injective g hg
  have hR:G.activeRows.card≤s:=by omega
  have hH:G.activeHubs.card≤s:=by omega
  have ha':2*G.activeRows.card*G.activeRows.card≤2*s*s:=Nat.mul_le_mul (Nat.mul_le_mul_left _ hR) hR
  have hh':G.activeRows.card*G.activeHubs.card≤s*s:=Nat.mul_le_mul hR hH
  nlinarith only [ha,hh,ha',hh']

end Oberwolfach
