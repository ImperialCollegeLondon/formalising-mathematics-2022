--import algebra.category.Module.basic
import linear_algebra.tensor_product
import ring_theory.noetherian

/-!

# Picard group of a commutative ring

Done with modules.

## Universes

Let's be brave and start using universes.

Instead of `Type`, which we've used all
through the course so far, let's start to
use a "more general Type universe" called
`Type u`. Here the so-called "universe"
`u` is just a natural number (but with much
less API).

Everything we've done so far for `Type`
all works for `Type u`; in fact `Type`
is just `Type 0`.

Some people call `Type u` a "Grothendieck universe".

-/

universe u

/-

Everything we do from now on will take place
in our fixed type universe `Type u` which
we'll never mention again.

## Modules
  
Let `R` be a commutative ring.

-/

variables (R : Type u) [comm_ring R]

/-

Definition: an R-module is just a vector space
over R.

Reminder: a vector space `M` over `R` is
a type `M`, plus a sensible way to add
vectors `m₁ + m₂ : M` together (`add_comm_group M`)
plus a sensible way to multiply a vector
by a scalar `r • m : M` (`module R M`)

-/

section module_basics

variables (M : Type u) [add_comm_group M] [module R M]
  (m₁ m₂ m : M) (r : R)

--#check m₁ + m₂ -- M
--#check r • m -- M

end module_basics

/- 

We want to put an equivalence relation on the type of all R-modules,
and the equivalence relation is "we are isomorphic".

Your instinct then is : let's write down the relation like this

-/

def module.r (M₁ : Type u) [add_comm_group M₁] [module R M₁] 
  (M₂ : Type u) [add_comm_group M₂] [module R M₂] : Prop :=
nonempty (M₁ ≃ₗ[R] M₂)


/-

But what is the actual type that this is a relation on? 
I guess it's some crazy pi type which will be hard to use.

-/

structure bundled_module (R : Type u) [comm_ring R] :=
(M : Type u)
[hA : add_comm_group M]
[hM : module R M]

attribute [instance] bundled_module.hA bundled_module.hM

def bundled_module.s : setoid (bundled_module R) :=
{ r := λ I J, nonempty (I.M ≃ₗ[R] J.M),
  iseqv := begin
    -- might be interesting for some people
    sorry
  end }

/-
This type is a bit difficult to deal with because the
typeclasses have been bundled into a structure instead
of the usual method of having them outside. This means
that the type class inference system (the square bracket system)
has a hard time dealing with them. Scott Morrison's idea
is that instead of relying on the typeclass system
(the square bracket system) we should use the category theory
system to manage all the boring stuff like "a module is
an additive monoid" behind the scenes.

In the `picard_with_categories` file we use Lean's implementation
`Module R` of `bundled_module R`. More precisely we use
bundled modules at universe level `u`, namely `Module.{u u} R`.

So I won't continue with this development.

Let's try and prove some key result about modules

-/

open_locale tensor_product

variables (M : Type u) [add_comm_group M] [module R M]
  (N : Type u) [add_comm_group N] [module R N]

def module.is_inverse : Prop :=
nonempty (M ⊗[R] N ≃ₗ[R] R)

/-
What's the idea? `i : M ⊗ N ≃ₗ[R] R`
Consider the following map from M to the generators
First send `m : M` to `mn ⊗ᵗ m : (M ⊗ N) ⊗ M`. This is an isomorphism
from `M` to `(M ⊗ N) ⊗ M`
and note that the image of `m` is of the form `(∑ⱼ rⱼ•m_ⱼ⊗ᵗnⱼ) ⊗ᵗ m`.
The corresponding element of `M ⊗ (N ⊗ M)` is `∑ⱼmⱼ⊗ᵗ(rⱼ•nⱼ⊗m)`
And this is isomorphic to `M` via `i.swap` or whatever it's called
So we have ended up with an isomorphism `M ≃ₗ M` with image in the
span of the `mⱼ`.

-/

--#print prefix linear_equiv

instance : has_coe (M ≃ₗ[R] N) (M →ₗ[R] N) := linear_equiv.linear_map.has_coe

--#check linear_map.rtensor

variables {R} {N} {P : Type u} [add_comm_group P] [module R P]

def linear_equiv.ltensor (e : N ≃ₗ[R] P) : (M ⊗[R] N ≃ₗ[R] M ⊗[R] P) :=
{ to_fun := linear_map.ltensor M e.to_linear_map,
    map_add' := by simp {contextual := tt},
    map_smul' := by simp {contextual := tt},
  inv_fun := linear_map.ltensor M e.symm.to_linear_map,
  left_inv := λ x, begin
    change (linear_map.ltensor M e.symm.to_linear_map).comp (linear_map.ltensor M e.to_linear_map) x = _,
    rw ← linear_map.ltensor_comp, 
    have := linear_map.ltensor_id M N,
    rw linear_map.ext_iff at this,
    convert this x,
    ext y,
    simp,
  end,
  right_inv := 
  begin
    intro x,
    change (linear_map.ltensor M e.to_linear_map).comp (linear_map.ltensor M e.symm.to_linear_map) x = _, 
    rw ← linear_map.ltensor_comp,
    have := linear_map.ltensor_id M P,
    rw linear_map.ext_iff at this,
    convert this x,
    ext y,
    simp,
  end }

def linear_equiv.rtensor (e : N ≃ₗ[R] P) : (N ⊗[R] M ≃ₗ[R] P ⊗[R] M) :=
{ to_fun := linear_map.rtensor M e.to_linear_map,
    map_add' := by simp {contextual := tt},
    map_smul' := by simp {contextual := tt},
  inv_fun := linear_map.rtensor M e.symm.to_linear_map,
  left_inv := λ x, begin
    change (linear_map.rtensor M e.symm.to_linear_map).comp (linear_map.rtensor M e.to_linear_map) x = _,
    rw ← linear_map.rtensor_comp, 
    have := linear_map.rtensor_id M N,
    rw linear_map.ext_iff at this,
    convert this x,
    ext y,
    simp,
  end,
  right_inv := 
  begin
    intro x,
    change (linear_map.rtensor M e.to_linear_map).comp (linear_map.rtensor M e.symm.to_linear_map) x = _, 
    rw ← linear_map.rtensor_comp,
    have := linear_map.rtensor_id M P,
    rw linear_map.ext_iff at this,
    convert this x,
    ext y,
    simp,
  end }

def fg_of_inverse (i : module.is_inverse R M N): submodule.fg (⊤ : submodule R M) :=
begin
  unfreezingI {cases i},
  let mn := i.symm 1,
  have hmn : mn ∈ ⊤ := submodule.mem_top,
  rw ← tensor_product.span_tmul_eq_top at hmn,
  obtain ⟨T, hT, hTmn⟩ := submodule.mem_span_finite_of_mem_span hmn,
  choose pM pN h2 using hT,
  change ∀ ⦃a : M ⊗ N⦄ (Ha : a ∈ ↑T), pM Ha ⊗ₜ[R] pN Ha = a at h2,
  classical,
  let Mgens := finset.image (λ x : {x : M ⊗ N // x ∈ T}, @pM x.1 x.2) finset.univ,
  refine ⟨Mgens, _⟩,
  -- let's define an isomorphism M → M
  let e0 : M ≃ₗ[R] R ⊗ M := 
    (tensor_product.lid R M).symm,
  let e1 : R ⊗ M ≃ₗ[R] (M ⊗ N) ⊗ M := 
    i.symm.rtensor M,
  let e2 : M ⊗ N ⊗ M ≃ₗ[R] M ⊗ (N ⊗ M) :=
    tensor_product.assoc R M N M,
  let e3 : M ⊗ (N ⊗ M) ≃ₗ[R] M ⊗ (M ⊗ N) :=
    (tensor_product.comm R N M).ltensor M,
  let e4 : M ⊗ (M ⊗ N) ≃ₗ[R] M ⊗ R :=
    i.ltensor M,
  let e5 : M ⊗ R ≃ₗ[R] M :=
    tensor_product.rid R M,
  let e : M ≃ₗ[R] M :=
    e0.trans (e1.trans (e2.trans (e3.trans (e4.trans e5)))),
  rw eq_top_iff,
  rintro m -,
  have hm : e (e.symm m) = m := e.to_equiv.apply_symm_apply m,
  rw ← hm,
  simp [e] at hm,
  sorry,
end
