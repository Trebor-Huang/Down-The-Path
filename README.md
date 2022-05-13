# [Down The Path](https://youtu.be/2ubIhBZG9NA)

> I was walking down the line,  
> Trying to find some peace of mind.  
> Then I saw you,  
> You were takin' it slow,  
> And walkin' it one step at a time.

A spartan implementation of H.O.T.T.

## Quick Examples

> "If you're lost now,  
> Maybe I could help you along and sing you a song,  
> And move you on."

I haven't implemented parsers for whole files yet. But I can already parse and print individual terms.

Ordinary MLTT stuff:
```
λ (t : U) (x : t) => x
Π (t : U) (x : t) => t
```
Dependent pairs are annotated the type of the second component with a peculiar syntax.
```
λ (t : U) (x : t) => t { t' => t' } x
Π (t : U) (x : t) Σ (t' : U) => t'
```
`fst` and `snd` are prefixes that have the highest priority, so `f fst snd p q` stands for `(f(fst(snd(p))))(q)`:
```
λ (T : U) (S : Π (_ : T) => U) (p : Σ (t : T) => S t) => snd p
Π (T : U) (S : Π (_ : T) => U) (p : Σ (t : T) => S t) => S fst p
```
`ap` and `Id` without dependency:
```
ap[ . y]
Id[ . A][y, y]
```
When we deal with n-ary `ap` and `Id`, we need to explicitly mark the LHS and RHS of the equations:
```
ap[z / ap[ . x] : x == x . y]
Id[z / ap[ . x] : x == x . A][y, y]
```
And of course this one reduces to the one *above* it.

## Type Theory

> She said  
> "I'm looking for a kind of shelter,  
> No place for me to call my own.  
> I've been walking all night long, but  
> I don't know where to call my home."

- [X] Start out with 0,1,∑,∏,U. (2, Nat are slightly more complicated.)
- [X] Add `Id` and `ap`. Define `1-1-Corr`.
- [ ] Add typechecking and reduction rules for `ap`.
  - [X] Easy rules for 0,1,∑,∏.
  - [ ] The complicated ones for U. We might need to introduce a couple more primitives (`corrL` and `corrR`). I'm not sure whether this would make it easier.
- [ ] Symmetries.
- [ ] Inductive types.
- [ ] Higher inductive types.
- [ ] Inductive families?!

Thorsten Altenkirch et al. in their original presentation stated that there are "philosophical, syntactic, and semantic" reasons that they used an `newtype` style approach when dealing with univalence, having `p↑↓ ≡ p`. I have no philosophical objections to these unless someone convinces me (which they didn't attempt); I anticipate some strictness issues that may have to be worked around by weird tricks
e.g. [Scott's trick](https://en.wikipedia.org/wiki/Scott's_trick), but this is purely semantic, and I don't need to worry yet; There may be confluence / termination / subject reduction problems, but I cannot yet see why. So I'm going to get rid of this `↑` `↓` stuff.

For inductive types (even `2`), we need to make `Id`, `ap` stuck on neutral terms. So for instance `Id[. A+B][inl a, inl b]` would compute to `Id[.A][a,b]`, just as the HoTT book describes. Alternatively we can just make `Id` compute into a case analysis. Not sure which would be easier.

The code files have some comments at the top where you can read a little more about my thoughts.

## Implementation

> "The only way to find that place is  
> Close to where my heart is.  
> I know I'm gonna get there,  
> But I've got to keep on walking down the line."

Python has got a couple of cool features like [assignment expressions](https://peps.python.org/pep-0572/) and [structural pattern matching](https://peps.python.org/pep-0634/). I'm trying to write python code in a semi-pure style.

## Down the line

> I said  
> "You go on walking down the line,  
> Wasting all your precious time.  
> But you're never gonna find it,  
> Because there is no end to the line,  
> There's no destination for to find."

(...)
