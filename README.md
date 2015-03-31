# stop2015-redex
PLT Redex model of basic Dependently Typed Racket calculus

Similar to calculus presented in Tobin-Hochstadt & Felleisen's 'Logical Types for Untyped Languages' from ICFP 2010, but with modifications to support refinement types and linear inequalities

## Files
- dtr-lang.rkt: language definition and helpers
- dtr-optypes.rkt: types for primitive operations
- dtr-logic.rkt: definitions of key judgements (proves, subtyping, update, etc...)
- dtr-fme.rkt: interface to linear inequality operations (which use fourier-motzkin elimination, hence 'fme')
- fme-bridge.rkt: file that performs conversions bewteen plt redex model representations and 'fme' package representations of linear inequalities
- dtr-tc.rkt: typing judgements (algorithmic)
- dtr-tests-basic.rkt: basic tests for functionality
- dtr-tests-tc.rkt: typechecking tests (all from ICFP 2010 + some checking linear inequalities and vector bounds, etc)

## Installation
1. Requires Racket (v6.1.1 certified, may work on earlier versions as well)
2. requires 'fme' racket package (use 'raco pkg install fme' to install)
3. clone git repo
4. in directory, run 'racket dtr-tests-basic.rkt && racket dtr-tests-tc.rkt' to verify all is well
