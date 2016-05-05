I try to explain the groupoid interpretation here, cause I can't wait until friday...

First, let me remind you what a category is.
A category has two things (objects and morphisms) and an operator between morphisms (composition).
f     : A -> B
g     : B -> C
--------------
g . f : A -> C

And there are two extra conditions:
1) every object has an identity morphism. By identity, I mean when composed with any other morphism (f), you get back the same morphism (f).
1(A) : A -> A
f    : A -> B
---------------------
f . 1(A) = f : A -> B

1(B) : B -> B
f    : A -> B
---------------------
1(B) . f = f : A -> B
(You need to check both left and right compositions!)
2) composition should be associative.
f : A -> B
g : B -> C
h : C -> D
----------------------------------
h . (g . f) = (h . g) . f : A -> D

Now consider the propositional equality on a certain type A. We claim that this is a category. Its objects are terms of type A, and its morphisms are proofs of two terms are propositional equal. For example,
p : Id(A, x, y)
then p is a morphism from x to y:
p : x -> y

So how to define the composition of two morphisms?
p         : Id(A, x, y)
q         : Id(A, y, z)
-----------------------
trans q p : Id(A, x, z)

Here we call the composition of morphisms 'trans', instead of writing
q . p
we write:
trans q p

So 'trans' is a function from a proof of Id(A, x,y) and a proof of Id(A, y,z) to a proof of Id(A, x,z):
trans : (Id(A, y,z), Id(A, x,y)) -> Id(A, x,z)
Or you can say that it's a proposition (PAT, of course!):
trans : (y = z /\ x = y) -> x -> z
'trans' is just the transitivity of propositional equality!!!

Prove 'trans' in Idris by yourself, it should look like:
trans : {A : Type} -> {x y z : A} -> (y = z) -> (x = y) -> (x = z)

Once we defined the objects, morphisms and composition between morphisms, we need to prove those two extraa conditions of category.

First we need to know what is an identity morphism for a object (let's say x).

It's trivial! The identity morphism is just (refl x)!
Now prove by yourself that:
1(x) : x -> x
f    : x -> y
-------------
f . 1(x) ~ f
which translated to idris should be:
leftIdentity : 
  {A : Type} -> {x y : A} ->
    (f : x = y) -> trans f (refl x) = f
define 'rightIdentity' by yourself and prove it!

You may notice that I hesitate not to write = for
 f . 1(x) ~ f
but using ~ instead. The reason is that this equality is the propositional equality which happens at one level up! This equality should really be written as:
 Id(Id(A,x,y), f . 1(x), f)
(the notation is mixed here, I know, it would be too long if I using type theory notations...)
The equality between morphisms/paths requires next level of morphisms/paths is why this groupoid is called WEAK infinity groupoid!

Now you can image I would ask you to prove associativity of compositions (trans):
f : x -> y
g : y -> z
h : z -> w
-------------------------
h . (g . f) ~ (h . g) . f
which could be translated to:
trans_associativity :
  {A : Type} -> {f : x = y} -> {g : y = z} -> {h : z = w} ->
    trans h (trans g f) = trans (trans h g) f
Proof it!

Now we proved that this is really a category, now comes the groupoid part.
A groupoid is a category where every morphism is inversible!
So first let me define inverse in category theory, a morphism 'f 'is inversible if composing it with its inverse gives you back the identity morphism:
f   : x -> y
f⁻¹ : y -> x
-----------------------
f . f⁻¹ = 1(y) : y -> y

f   : x -> y
f⁻¹ : y -> x
-----------------------
f⁻¹ . f = 1(x) : x -> x

So now we need to define an inverse operator first and then prove the inverse operator really works! We call the inverse operator 'sym',
sym : x = y -> y = x
You guess what's that? It's the symmetry of Identity Path/Type!

Write down the propositions for left and right inverse and prove them!

WHOOP! You proved the groupoid structure! Congratulations!

What's next?

How about the functors between those categories?
So what's a functor?

A functor is a morphism between two categories which preserve the structure of a category. If we call a category (whose objects are terms of type A) Cat(A), and another category Cat(B), then a functor is:
F : Cat(A) -> Cat(B),
which maps objects to objects and morphisms to morphisms (so basically we need two functions, one for objects another for morphisms). For morphisms it preserves the connectivity, which just means
  p :   x ->   y
----------------
F p : F x -> F y

Also, the functor should respects the composition operator on morphisms.
  h =   g .   f
---------------
F h = F g . F f
Finally, the functor should respect the identity morphisms.
1(x) : x -> x
---------------
F 1(x) = 1(F x)

That's all you need for functors! (For us, we may want something more because we want a morphism between two groupoid, but I don't know if you need to check that the morphism should manually check morphism/functor respect inverse or inverse can be deduced by the above conditions.)

So how can we define such a functor? Well, we guess ... the functor is ...






Just the functions between type A and B!!!

A function 'f' : A -> B surely maps terms of type A to type B, but would it map morphisms to morphisms? 'f' could not be applied to a proof of a propositional equality... So we need another function.

Well, thinking about List. We claim that List is a functor, it's a functor from a category to itself (endofunctor...) it maps a type A (objects in the category) to another type List A. And there's another higher order function map:
 map : (A -> B) -> (List A -> List B)
that maps a morphism/function between two objects/types to another morphism
in the same category.

So we need some function like 'map' (but things are a bit different here though, because the functor we need is not an endofunctor). It takes a morphism/identity type on A to an identity type on B.

So the thing we need is called 'resp'.
     F :   A ->  B
     p :   x =   y
------------------
resp p : F x = F y

So again 'resp' is a function:
resp :
 {A B : Type} -> {x y : A} -> (F : A -> B)
   -> x = y -> F x = F y
Proof it!

Now we need to resp preserve the identity morphisms.
1(x) : x -> x
---------------
F 1(x) = 1(F x)
here I still use the same F to denote resp F just for convenience.
This should translated to:
resp_id :
  {A B : Type} -> {x : A} -> (F : A -> B) ->
    x = x -> resp F (refl x) = refl (F x)

Then prove
  h =   g .   f
--------------- functor respects composition
F h = F g . F f
here I still use the same F to denote resp F just for convenience.
This should translated to:
resp_trans :
  {A B: Type} -> {x y z : A} -> (F : A -> B)
     -> (f : x = y)
     -> (g : y = z)
     -> (h : x = z)
     ->        h = trans         g          f
     -> resp F h = trans (resp F g) (resp F f)

Now we can claim a function f is really a functor between the two categories...






So why we care about this?
Because now we can say that a type is a groupoid, and a function is a functor between groupoids. Now types has structures!
Before when we talking about types, types are just a kind of thing like set. for example Nat,
If you just look at the introduction rule:
          n : Nat
------- --------- Nat-intro
z : Nat s n : Nat
 
You may just see z, s(z), s(s(z)), s(s(s(z)), ...., etc.
You think that's all? NO! That's not all of it.
If you look harder you may also see things like:
3 + 4, 8*9, factorial(5), etc,
if you look even harder you may see things like:
x + y, factorial(x), given x and y is Nat.
But still it's not so interesting. Now it's totally different! With the help of groupoid interpretation. In addition to the objects/terms, we also have morphisms!!!!! It's like a big net where each vertex represent a term and the edge represent the path/proof of identity types.

Now rethinking the identity types again. From the introduction rule
x : A
-------------------- Id-intro
refl x : Id(A, x, x)
we may just see the diagonal objects. But that's not the whole picture. Given a type A, we now have a groupoid. it's morphism are proofs of x y. All the morphisms forms the set of objects of Id(A, x, y). So a type is its objects together with the path (proofs of equality) between those objects!!!!

Also if you go one level up (I mean if think the morphism between objects of Id(A, x, y)), those also forms a groupoid. Every specific identity type also forms a groupoid (remember Id is a type family, when you fill in the 'x' and 'y' you get a specific identity type). Isn't that amazing.

 What can I do with this interpretation. I am not quite sure yet...
but I have a blur intuition that higher inductive types has something to do with it.
Because for ordinary inductive types, we define types in terms of its constructors. But for higher inductive types, we also define its path/identity types while defining the types. Why not? Because we know types are groupoid, which is just a net of identity path (this is my understanding).

That's all for today. It's 2 o'clock I need go to sleep now...
