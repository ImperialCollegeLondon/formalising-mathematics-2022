import combinatorics.simple_graph.connectivity

universe u

namespace simple_graph

namespace walk

open simple_graph

variables {V : Type u} [decidable_eq V] {G : simple_graph V} {v : V} {p : G.walk v v}

lemma nil_ne_cycle : ¬ (walk.nil : G.walk v v).is_cycle :=
λ h, is_circuit.ne_nil h.to_circuit rfl

namespace is_cycle

def next_vertex (hp : p.is_cycle) : V :=
walk.get_vert p 1

lemma next_vertex_adj (hp : p.is_cycle) : G.adj v hp.next_vertex :=
begin
  rcases p with v | ⟨_, w, _, padj, pwalk⟩,
  { exact false.elim (nil_ne_cycle hp) },
  { convert padj,
    simp only [next_vertex, get_vert],
    cases pwalk; refl }
end

lemma eq_cons (hp : p.is_cycle) : ∃ q : G.walk hp.next_vertex v, 
 p = walk.cons (hp.next_vertex_adj : G.adj v hp.next_vertex) q :=
begin
  rcases p with v | ⟨_, w, _, padj, pwalk⟩,
  { exact false.elim (nil_ne_cycle hp) },
  { have hw : w = hp.next_vertex,
    { simp only [next_vertex, get_vert],
      cases pwalk; refl },
    simp [hw.symm],
    convert (⟨pwalk, heq_of_cast_eq rfl rfl⟩ : Exists _);
    { exact hw.symm, } }
end

end is_cycle

end walk

structure is_tree {V : Type u} (G : simple_graph V) : Prop :=
(nonempty : nonempty V)
(exists_unique_path : ∀ v w : V, ∃! p : G.walk v w, p.is_path)

namespace is_tree

variables {V : Type u} [decidable_eq V] {G : simple_graph V} {v : V}

lemma exists_path (hG : G.is_tree) (v w : V) : ∃ p : G.walk v w, p.is_path :=
exists_of_exists_unique $ hG.exists_unique_path v w

lemma no_cycles [decidable_eq V] (hG : G.is_tree) (u : V) (p : G.walk u u) : ¬ p.is_cycle :=
begin
  intro hcycle,
  obtain ⟨q, qpath, falsething⟩  := hG.exists_unique_path u hcycle.next_vertex,
  dsimp at falsething,
  cases hcycle.eq_cons with r hr,
  have hrpath : r.is_path,
  { rw hr at hcycle,
    cases hcycle,
    fsplit,
    swap, 
    convert hcycle_support_nodup,
    rw hr at hcycle,
    rw walk.is_cycle_def at hcycle,
    cases hcycle with h1 h2,
    exact walk.is_trail.of_cons h1,
  },
  -- plan : reverse r is path and foo below is path, contradicting falsething
  have foo := walk.cons hcycle.next_vertex_adj walk.nil,
  
  sorry
end

end is_tree

end simple_graph
