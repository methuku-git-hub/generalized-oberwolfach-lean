module

public import Oberwolfach.IndexedMarkedGraph
public import Mathlib.Logic.Function.Basic

@[expose] public section

/-! Construct the actual transformer input from two displayed realizations
of one balanced indexed graph. Only the first vertex realization is
injective; the second may identify vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U]
    [Fintype A] [Fintype S] [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

def indexedMarkedRootPair (G:IndexedMarkedGraph V₀ U₀ A S) (hG:G.IsBalanced m)
    (f g:V₀→V) (h k:U₀→U) (hf:Function.Injective f) (hh:Function.Injective h)
    (R R':Finset V) (B:Finset U)
    (hfR:∀ v,f v∈R) (hgR:∀ v,g v∈R') (hhB:∀ u,h u∈B) (hkB:∀ u,k u∈B)
    (hRR:Disjoint R R') (hcross:∀ x∈R,∀ y∈R',¬PermutationClose π b x y)
    (hubs:∀ s,h (G.hub s)≠k (G.hub s))
    (hsep:∀ a,¬PermutationClose π b (f (G.src a)) (f (G.dst a)))
    (hsep':∀ a,¬PermutationClose π b (g (G.src a)) (g (G.dst a)))
    (hri:Function.Injective (fun a=>if G.jr a then ({f (G.src a),π (f (G.dst a))}:Finset V) else {f (G.src a),f (G.dst a)}))
    (hri':Function.Injective (fun a=>if G.jr a then ({g (G.src a),π (g (G.dst a))}:Finset V) else {g (G.src a),g (G.dst a)}))
    (hsi:Function.Injective (fun s=>(f (G.row s),h (G.hub s))))
    (hsi':Function.Injective (fun s=>(g (G.row s),k (G.hub s))))
    (ha:∀ a,if G.jr a then
      (∃ e,ktail e=f (G.src a)∧khead e=f (G.dst a))∧(∃ e,ktail e=g (G.src a)∧khead e=g (G.dst a))
      else (∃ e,tail e=f (G.src a)∧head e=f (G.dst a))∧(∃ e,tail e=g (G.src a)∧head e=g (G.dst a)))
    (hs:∀ s,if G.js s then HK (f (G.row s)) (h (G.hub s))∧HK (g (G.row s)) (k (G.hub s))
      else H₀ (f (G.row s)) (h (G.hub s))∧H₀ (g (G.row s)) (k (G.hub s))):
    MarkedRootPair tail head ktail khead H₀ HK π b m A S:=by
  let φ:=Function.extend f g id
  let ψ:=Function.extend h k id
  have hφ:∀ v,φ (f v)=g v:=fun v=>hf.extend_apply g id v
  have hψ:∀ u,ψ (h u)=k u:=fun u=>hh.extend_apply k id u
  have hbase:=G.map_balanced m hG f h
  refine {
    src:=f∘G.src,dst:=f∘G.dst,row:=f∘G.row,φ:=φ,ψ:=ψ,u:=h∘G.hub,u':=k∘G.hub,jr:=G.jr,js:=G.js,
    R:=R,R':=R',B:=B,disjointRows:=hRR,
    rimRoots:=?_,spokeRoots:=?_,hubRoots:=?_,hubMap:=?_,differentHubs:=hubs,
    sourceArcSeparation:=hsep,imageArcSeparation:=?_,fourRootSeparation:=?_,
    rowBalance:=fun v=>⟨hbase.directed v,hbase.row v⟩,markedRowBalance:=?_,hubBalance:=hbase.hub,
    sourceRimInjective:=hri,imageRimInjective:=?_,sourceSpokeInjective:=hsi,imageSpokeInjective:=?_,
    rimPresent:=?_,spokePresent:=?_}
  · intro a;simpa only [Function.comp_apply,hφ] using
      (show f (G.src a)∈R∧f (G.dst a)∈R∧g (G.src a)∈R'∧g (G.dst a)∈R' from ⟨hfR _,hfR _,hgR _,hgR _⟩)
  · intro s;simp only [Function.comp_apply,hφ];exact ⟨hfR _,hgR _⟩
  · intro s;exact ⟨hhB _,hkB _⟩
  · intro s;exact (hψ _).symm
  · simpa only [Function.comp_apply,hφ] using hsep'
  · intro a x hx y hy hxy
    simp only [Function.comp_apply,hφ,Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl
    all_goals first | exact False.elim (hxy rfl) | exact hsep a | exact hsep' a |
      exact (hsep a) ∘ (permutationClose_symm π b _ _).mp | exact (hsep' a) ∘ (permutationClose_symm π b _ _).mp |
      exact hcross _ (hfR _) _ (hgR _) | exact (hcross _ (hfR _) _ (hgR _)) ∘ (permutationClose_symm π b _ _).mp
  · intro v
    rw [finite_typed_fiber_filter_card,finite_typed_fiber_filter_card]
    exact hbase.marked v
  · simpa only [Function.comp_apply,hφ] using hri'
  · simpa only [Function.comp_apply,hφ] using hsi'
  · simpa only [Function.comp_apply,hφ] using ha
  · simpa only [Function.comp_apply,hφ] using hs

end Oberwolfach
