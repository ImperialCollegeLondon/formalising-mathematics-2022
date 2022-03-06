import algebra.category.Module.basic
import data.matrix.basic -- we're going to do matrices
import data.real.basic -- with coefficients in the real numbers
import linear_algebra.tensor_product

/-!

# Picard group of a commutative ring done with categories

A group is a set with some structure (in Lean we say
a type with some structure). A category is 
just the same -- it's a type with some structure.

## Definition of a category

A category is a type `C` equipped with the following
extra structure:

* For every pair of terms `x y : C`, a set `x ⟶ y` 
  of "abstract arrows from `x` to `y`". Note that 
  this is *not* the usual `\r` implication arrow;
  this is a weird new arrow `\hom`.

* For every `x : C`, a special abstract arrow `𝟙 x : x ⟶ x`
  called "the identity map" by mathematicians and `id` by Lean.

* For every `x y z : C` and every pair of abstract
arrows `f : x ⟶ y` and `g : y ⟶ z`, an abstract 
"composition arrow" `f ≫ g : x ⟶ z`, called `comp` by Lean.

* Such that the axioms `id_comp`, `comp_id` and `comp_assoc`
  are satisfied. Exercise: guess what these axioms say.

  Exercise: look up the axioms of a monoid. Is
  a category a monoid?
-/

universe u

open category_theory

variables (C : Type u) [category C] (x y z : C)
  (f : x ⟶ y) (g : y ⟶ z)

--#check 𝟙 x -- x ⟶ x
--#check f ≫ g -- x ⟶ z

/-

# Example of a category

First I need to tell you the type for the category,
and the type is the natural numbers.

Next, given two natural numbers `m` and `n`, I
define the set `m ⟶ n` to be the `n` by `m` matrices with real
coefficients.

We continue with the structure we need to make this
into a category. We need to define the identity arrow
`n ⟶ n` if `n` is a natural number, and of course we use
the `n × n` identity matrix.

Finally we need to define composition of arrows.
We do this as follows. If `A : m → n` is an `n × m`
matrix and and `B : n → p` is a `p × n` matrix,
we define `A ≫ B` to be the `p × n` matrix `B * A`.

Can you check to see that this gives the natural numbers
the structure of a category?

-/

example : category ℕ :=
{ hom := λ m n, matrix (fin n) (fin m) ℝ,
  id := λ n, (1 : matrix (fin n) (fin n) ℝ),
  comp := λ m n p A B, matrix.mul B A,
  id_comp' := begin
    sorry
  end,
  comp_id' := begin
    sorry
  end,
  assoc' := begin
    sorry
  end }

/- 

Here's another approach. Why don't we define the
abstract arrows not to be matrix rings but to be
actual linear maps -- "a different way of looking
at the same thing".

-/

example : category ℕ :=
{ hom := λ m n, (fin m → ℝ) →ₗ[ℝ] (fin n → ℝ),
  id := λ n, linear_map.id,
  -- comp comes out backwards because the traditional
  -- notation for writing functions is on the left
  -- `f(x)`.
  comp := λ m n p hmn hnp, linear_map.comp hnp hmn,
  id_comp' := begin
    sorry,
  end,
  comp_id' := begin
    sorry,
  end,
  assoc' := begin
    sorry,
  end }

-- 
/-

If `R` is a ring in universe `u`, then
`Module.{u u} R` (hitherto abbreviated to `Module R`)
is the type of `R`-modules in universe `u`.

Unsurprisingly, if `M N : Module R` then
the opaque arrow type `M ⟶ N` is just defined to mean
`M →ₗ[R] N`, the type of `R`-linear maps from `M` to `N`.

## Isomorphisms in categories

An *isomorphism* `x ≅ y` in a category is a pair
of arrows `to_fun : x ⟶ y` and `inv_fun : y ⟶ x`
such that `to_fun ≫ inv_fun = 𝟙 _` and `inv_fun ≫ to_fun = 𝟙 _`

For example if `m` and `n` are natural numbers in our
example category, there are no isomorphisms `m ≅ n` at all
if `m ≠ n`, but there are many isomorphisms `n ≅ n`, one
for every invertible real `n × n` matrix.

Let's define the "we are isomorphic" equivalence relation
on the elements of our category. Hint: the key construction
for the `refl` proof is `iso.refl`. What do you think the
key constructions for `symm` and `trans` will be?

-/

/-- the setoid structure for being isomorphic in a category -/
def category_theory.s : setoid C :=
{ r := λ M N, nonempty (M ≅ N),
  iseqv := begin
    sorry,
  end }

/-

# Quotient categories

Sometimes we put equivalence relations on groups.
For example if `H : subgroup G` then we can partition
`G` into the left cosets `gH` of `H`, and the equivalence
relation associated to the partition is `g₁ ≈ g₂ ↔ g₁⁻¹ * g₂ ∈ H`.
We can also partition `G` into the right cosets of `H`
and get a different (in general) equivalence relation.

If you have a group with an equivalence relation on it,
then you can quotient out the group by the equivalence
relation to get a quotient type, and then we can ask
the question of whether the multiplication on the group "descends"
(or as Lean calls it, "lifts" :-( ) to a multiplication
on the quotient, giving us what mathematicians call a
quotient group.

This "descent of multiplication" is not automatic. For example
there is in general no natural multiplication on the set of
left cosets of a group by a subgroup. The same is true
for the right cosets. If however the subgroup `H`
is *normal*, then the left cosets and the right cosets
coincide, the two equivalence relations become equal,
and this is the key thing needed to make the
calculation work; the multiplication descends and we get
a quotient group. 

The axiom on an equivalence relation on a group
which is necessary and sufficient for the multiplication
to descend to the quotient is called "being a congruence
relation". Congruence relations in Lean are called `con`.
They were developed by Amelia Livingston as part of her work with me
defining schemes in Lean.

-/

/-

# The category of R-modules

This is `bundled_modules R` from last time. It's the
type of all `R`-modules.

-/

variables (R : Type u) [comm_ring R]

#check Module.{u u} R -- Type (u+1)

/-

Ooh -- a universe bump!

The "set of all real vector spaces" isn't a set because
of stupid reasons to do with sets being elements of themselves.
Mathematicians often say "it's too big to be a set". What's
going on is that it is a type, but in the next universe up.

-/

open category_theory

def Module.one : Module.{u u} R := Module.of R R

instance : has_one (Module.{u u} R) :=
{ one := Module.one R }

open_locale tensor_product

def Module.mul (M N : Module.{u u} R) : Module.{u u} R :=
Module.of R (M ⊗[R] N)

/-- Activate notation `*` for R-modules (it's tensor product).  -/
instance : has_mul (Module.{u u} R) :=
{ mul := Module.mul R }

-- impossible to make in Lean
-- example : monoid (Module.{u u} R) :=
-- { mul := (*),
--   one := 1,
--   mul_assoc := begin
--     intros M N P,
--     -- aargh this isn't true
--     -- (M ⊗ N) ⊗ P and M ⊗ (N ⊗ P) are
--     -- isomorphic but might not be *equal*
--     sorry
--   end,
--   one_mul := sorry, -- probably not true
--   mul_one := sorry, -- probably not true
-- }

open Module

def Module.category.con : con (Module.{u u} R) :=
{ mul' := begin
    rintro M N P Q ⟨eMN⟩ ⟨ePR⟩,
    change nonempty (of R (M ⊗[R] P) ≅ of R (N ⊗[R] Q)),
    replace eMN := eMN.to_linear_equiv,
    replace ePR := ePR.to_linear_equiv,
    exact ⟨{ 
      hom := tensor_product.map eMN ePR,
      inv := tensor_product.map eMN.symm ePR.symm,
      hom_inv_id' := begin
        convert (tensor_product.map_comp _ _ _ _).symm,
        simp,
        refl, 
      end,
      inv_hom_id' := begin
        convert (tensor_product.map_comp _ _ _ _).symm,
        simp,
        refl,
      end }⟩,
  end,
  ..category_theory.s (Module.{u u} R) }

instance : setoid (Module.{u u} R) := (Module.category.con R).to_setoid 

abbreviation Module.Picard_monoid := (Module.category.con R).quotient

-- We can't get an induced monoid structure on `Module.Picard_monoid`
-- from some `monoid (Module.{u u} R)` term, because there is no
-- such natural term. We will have to make this ourselves
instance : monoid (Module.Picard_monoid R) :=
{ mul := (*),
  mul_assoc := begin
    intros a b c,
    apply quotient.induction_on₃ a b c, clear a b c,
    intros M N P,
    suffices : ⟦(M * N) * P⟧ = ⟦M * (N * P)⟧,
    { simpa, },
    apply quotient.sound,
    apply nonempty.map (linear_equiv.to_Module_iso'),
    use tensor_product.assoc R M N P,
  end,
  one := ⟦1⟧,
  one_mul := begin
    intro a,
    apply quotient.induction_on a, clear a,
    intro M,
    suffices : ⟦1 * M⟧ = ⟦M⟧,
    { simpa },
    apply quotient.sound,
    apply nonempty.map (linear_equiv.to_Module_iso'),
    use tensor_product.lid R M,
  end,
  mul_one := begin
    intro a,
    apply quotient.induction_on a, clear a,
    intro M,
    suffices : ⟦M * 1⟧ = ⟦M⟧,
    { simpa },
    apply quotient.sound,
    apply nonempty.map (linear_equiv.to_Module_iso'),
    use tensor_product.rid R M,
  end,
}

/-- The Picard group of a ring (defined via modules) -/
abbreviation Module.Picard_group := units (Module.Picard_monoid R)

-- doesn't trigger automatically because of the R parameter I guess?
instance : group (Module.Picard_group R) := units.group

-- we lost a universe level!
#check Module.Picard_group R -- Type (u + 1)

-- It's a group, but it's in a universe one higher than where we started
-- because we went via the "class" of all R-modules. 

