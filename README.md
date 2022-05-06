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

(...)

## Type Theory

> She said  
> "I'm looking for a kind of shelter,  
> No place for me to call my own.  
> I've been walking all night long, but  
> I don't know where to call my home."

- [X] Start out with 0,1,∑,∏,U. (2, Nat are slightly more complicated.)
- [X] Add `Id` and `ap`. Define `1-1-Corr`.
- [ ] Add typechecking and reduction rules for `ap`.
- [ ] Symmetries......
- [ ] Inductive types.
- [ ] Higher inductive types.
- [ ] Inductive families?!

Thorsten Altenkirch et al. in their original presentation stated that there are "philosophical, syntactic, and semantic" reasons that they used an `newtype` style approach when dealing with univalence, having `p↑↓ ≡ p`. I have no philosophical objections to these unless someone convinces me (which they didn't attempt); I anticipate some strictness issues that may have to be worked around by weird tricks
e.g. [Scott's trick](https://en.wikipedia.org/wiki/Scott's_trick), but this is purely semantic, and I don't need to worry yet; There may be confluence / termination / subject reduction problems, but I cannot yet see why. So I'm going to get rid of this `↑` `↓` stuff.

The code files have some comments at the top where you can read a little more about my thoughts.

## Implementation

> "The only way to find that place is  
> Close to where my heart is.  
> I know I'm gonna get there,  
> But I've got to keep on walking down the line."

(...)

## Down the line

> I said  
> "You go on walking down the line,  
> Wasting all your precious time.  
> But you're never gonna find it,  
> Because there is no end to the line,  
> There's no destination for to find."

(...)
