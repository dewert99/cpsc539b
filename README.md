The type system is a combination of λβ from the refinement typing paper and system F.  It also supports refining arbitrary types (instead of just base types), but these refinements can't mention the term they refine (only other terms in scope).  There is also an experimental feature that allows lambda terms that appear as the argument of an application to be checked directly instead of being inferred.

The syntax is
```
ident := "a string literal"
lit := #t | #f | 0 | 1 | -1 | 2 | -2 | ..
pred := (+ pred pred) | (sub pred pred) | (<= pred pred) | (= pred pred) | (and pred pred) | (or pred pred) | (if pred pred pred) | res | ident | lit
type := (: type pred) | (-> ident type type) | (forall ident type) | ident | int | bool
term := (let ((ident term)..) term) | (letrec ((ident term)..) term) | (λ (ident..) term) | (term..) | (inst term (type..)) | (if term term term) | (as term type) | ident | lit
command := anf | check | vcheck | (define ident term) | term
```
The cli accepts commands:
* `term` => sets the term as the active program
* `check` => type check the active program
* `vcheck` => type check the active program verbosely
* `anf` => convert the active program to a normal form
* `(define ident term)` => anf and type check the term, and if it type-checks add it to the global context, doesn't allow redefinitions

The global context when starting the program is:
```
"sub": (-> "x" (: int #t) (-> "y" (: int #t) (: int (= res (- "x" "y")))))
"add": (-> "x" (: int #t) (-> "y" (: int #t) (: int (= res (+ "x" "y")))))
"le": (-> "x" (: int #t) (-> "y" (: int #t) (: bool (= res (<= "x" "y")))))
"assert": (-> "x" (: bool res) (: bool res))
"eq": (-> "x" (: int #t) (-> "y" (: int #t) (: bool (= res (= "x" "y")))))
```
