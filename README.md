# M1P1-lean
Material from M1P1, formalised in Lean

I am writing heavily-commented Lean proofs of results from Imperial's M1P1 course, and example sheet questions. The general aim is to turn the material into a fully formalised mathematics textbook covering basic 1st year analysis.

I will be giving talks about this repository on Tuesdays 1-2 in Huxley 140 during the Spring 2019 term.

Kevin Buzzard

# Installation instructions

First you need to install Lean and and the mathlib helper scripts, by following the instructions [here at the mathlib github repository](https://github.com/leanprover-community/mathlib#installation).

Once you have these, you can install this project with the following incantations:

```
git clone git@github.com:ImperialCollegeLondon/M1P1-lean.git
cd M1P1-lean
leanpkg configure
update-mathlib
```
