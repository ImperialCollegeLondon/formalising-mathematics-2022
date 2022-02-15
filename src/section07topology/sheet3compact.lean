/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
-- the next import will be enough for this sheet
import topology.subset_properties -- compactness of subsets of top spaces

/-!

# Continuous image of compact is compact

-/

/-!

# Topology, the traditional way

Let's do some topology! In this file we prove that 

* the continuous image of a compact space is compact;
* A closed subset of a compact space is compact.

## Details

In fact we do a little more than this (but it's basically equivalent).
We do not work with compact topological spaces, we work with compact
subsets of topological spaces. What we will actually prove is this:

* If `f : X → Y` is a continuous map, and `S : set X` is a compact subset
(with the subspace topology), then `f '' S` (the image of `S` under `f`) is
compact (with the subspace topology).

* If `X` is a topological space, if `S` is a compact subset and if `C` is
a closed subset, then `S ∩ C` is a compact subset.

The original results are just the special case where `S` is `univ : set X`.
-/

-- Let X and Y be topological spaces, and let `f : X → Y` be a map.
variables (X Y : Type) [topological_space X] [topological_space Y] (f : X → Y)

-- I don't want to be typing `set.this` and `set.that` so let's open
-- the `set` namespace once and for all.
open set

/-!

## Compact subspaces

`is_compact` is a predicate on `set X`, if `X` is a topological space. 
In other words, `is_compact X` doesn't make sense, but if `S : set X`
then `is_compact S` does. The actual definition in mathlib involves
filters! But it is a theorem in mathlib that `is_compact S` is true if and only
if every collection of open subsets of `X` whose union contains `S`
has a finite subcollection whose union contains `S`. Unfortunately,
mathlib's version of this, `compact_iff_finite_subcover`, uses a slightly
wacky notion of finite subcover involving `finset X`, the type of finite
subsets of `X` (a completely different type to the type `set X`!).
We prove an easier-to-use version involving `finite Z`, the predicate
saying that `Z : set ι` is finite. You can ignore this proof.
-/



/-!

## Continuous image of compact is compact

I would start with `rw compact_iff_finite_subcover' at hS ⊢,`

The proof that I recommend formalising is this. Say `S` is a compact
subset of `X`, and `f : X → Y` is continuous. We want to prove that
every cover of `f '' S` by open subsets of `Y` has a finite subcover.
So let's cover `f '' S` with opens `U i : set Y`, for `i : ι` and `ι` an index type.
Pull these opens back to `V i : set X` and observe that they cover `S`.
Choose a finite subcover corresponding to some `F : set ι` such that `F` is finite
(Lean writes this `h : F.finite`) and then check that the corresponding cover
of `f '' S` by the `U i` with `i ∈ F` is a finite subcover.

Good luck! Please ask questions (or DM me on discord if you don't want to 
ask publically). Also feel free to DM me if you manage to do it!

Useful theorems:

`continuous.is_open_preimage` -- preimage of an open set under a
continuous map is open.

`is_open_compl_iff` -- complement `Sᶜ` of `S` is open iff `S` is closed.

## Some useful tactics:

### `specialize`

`specialize` can be used with `_`. If you have a hypothesis

`hS : ∀ {ι : Type} (U : ι → set X), (∀ (i : ι), is_open (U i)) → ...`

and `U : ι → set X`, then

`specialize hS U` will change `hS` to 

`hS : (∀ (i : ι), is_open (U i)) → ...`

But what if you now want to prove `∀ i, is_open (U i)` so you can feed it
into `hS` as an input? You can put

`specialize hS _`

and then that goal will pop out. Unfortunately it pops out _under_ the
current goal! You can swap two goals with the `swap` tactic though :-)

### `change`

If your goal is `⊢ P` and `P` is definitionally equal to `Q`, then you
can write `change Q` and the goal will change to `Q`. Sometimes useful
because rewriting works up to syntactic equality, which is stronger
than definitional equality.

### `rwa`

`rwa h` just means `rw h, assumption`

### `contradiction`

If you have `h1 : P` and `h2 : ¬ P` as hypotheses, then you can prove any goal with
the `contradiction` tactic, which just does `exfalso, apply h2, exact h1`.

### `set`

Note : The `set` tactic is totally unrelated to the `set X` type of subsets of `X`!

The `set` tactic can be used to define things. For example
`set T := f '' S with hT_def,` will define `T` to be `f '' S`
and will also define `hT_def : T = f '' S`.

-/

/-
#check is_open_compl_iff
lemma image_compact_of_compact (hf : continuous f) (S : set X) (hS : is_compact S) :
  is_compact (f '' S) :=
begin
  -- proof I recommend:
  -- (1) cover f''s with opens. Want finite subcover
  -- (2) pull back
  -- (3) finite subcover
  -- (4) push forward

  -- start by changing `is_compact` to something we can work with.
  rw compact_iff_finite_subcover' at hS ⊢,
  -- Define `T` to be `f '' S` -- why not?
  set T := f '' S with hT_def,
  -- Now `T = f '' S` and `hT_def` tells us that.
  -- Note that `set T := ...` is about the *tactic* `set`.

  -- OK let's go.
  -- Say we have a cover of `f '' S` by opens `U i` for `i : ι`.
  intro ι,
  intro U,
  intro hU,
  intro hcoverU,
  
  -- Define `V i` to be the pullback of `U i`.
  set V : ι → set X := λ i, f ⁻¹' (U i) with hV_def,
  -- Let's check that the V's are open and cover `S`.
  specialize hS V _,
  -- first let's check they're open.
  { intro i,
    rw hV_def, dsimp only,
    apply continuous.is_open_preimage hf _ (hU i) },
  specialize hS _,
  -- Now let's check they cover `S`.
  { intros x hx,
    have hfx : f x ∈ T,
    { rw hT_def, 
      rw mem_image,
      use x,
      use hx },
    specialize hcoverU hfx,
    rw mem_Union at hcoverU ⊢,
    -- and now we could take everything apart and then re-assemble,
    -- but `x ∈ f⁻¹' U` and `f x ∈ U` are equal by definition!
    exact hcoverU -- abuse of definitional equality!
  },
  -- Now let's take a finite subset `F : set ι` such that the `V i` for `i ∈ F`
  -- cover S.
  rcases hS with ⟨F, hFfinite, hF⟩,
  -- I claim that this `F` gives us the finite subcover.
  use F,
  -- It's certainly finite.
  use hFfinite,
  -- Let's check it covers. Say `y : Y` is in `T`.
  rintros y ⟨x, hxs, rfl⟩,
  -- then `y = f x` for some `x : X`, and `x ∈ S`.
  rw subset_def at hF, -- this is definition so this line can be deleted.
  -- then x is in the union of the `V i` for `i ∈ F`.
  specialize hF x hxs,
  -- so it's in one of the `V i`
  rw mem_bUnion_iff at hF ⊢,
  -- and now we could take everything apart and then re-assemble,
  -- but `x ∈ f⁻¹' U` and `f x ∈ U` are equal by definition!
  exact hF,
end
-/

lemma image_compact_of_compact' (hf : continuous f) (S : set X) (hS : is_compact S) :
  is_compact (f '' S) :=
begin
  rw is_compact_iff_finite_subcover at *,
  intros ι U hU hcover,
  specialize hS (λ i, f⁻¹' (U i)) _ _,
  { intro i,
    exact continuous.is_open_preimage hf _ (hU i) },
  { intros x hx,
    specialize @hcover (f x) ⟨x, hx, rfl⟩,
    rw mem_Union at *,
    rcases hcover with ⟨i, hi⟩,
    use i,
    exact hi },
  cases hS with t ht,
  use t,
  rintro y ⟨x, hx, rfl⟩,
  specialize ht hx,
  rw mem_Union at *,
  rcases ht with ⟨i, hi⟩,
  rw mem_Union at hi,
  rcases hi with ⟨ht, hix⟩,
  use i,
  rw mem_Union,
  use ht,
  exact hix,
end

