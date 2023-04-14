Note: This is a course project for CPSC539B at UBC

The type system is a combination of λβ from the refinement typing paper and system F.  It also supports refining arbitrary types (instead of just base types), but these refinements can't mention the term they refine (only other terms in scope).  There is also an experimental feature that allows lambda terms that appear as the argument of an application to be checked directly instead of being inferred.  Terms bound in letrec must have function type to avoid issue discussed in class. It doesn't include a type abstraction term, but infers them when checking against a forall type (in checking mode). It also doesn't support shadowing type variables.

The syntax is
```
ident := "a string literal"
lit := #t | #f | 0 | 1 | -1 | 2 | -2 | ..
pred := (+ pred pred) | (- pred pred) | (<= pred pred) | (= pred pred) | (and pred pred) | (or pred pred) | (if pred pred pred) | res | ident | lit
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

Run with
```
docker build .
docker run -it <name of docker image>
```

### Examples
Some example programs can be found in [`main.rs`](src/main.rs)
* `test_ty_check!` is used for programs where type checking should succeed.
* `test_ty_check_result!` is used for programs where type checking should fail.

### Type System Details
[type_system.pdf](type_system.pdf) contains the type derivation trees for the type system after running anf. 
