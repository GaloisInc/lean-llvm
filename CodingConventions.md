This document captures specific coding conventions expected on Lean code in
the VADD project.  In general, we aim to follow the practices in the Lean
source base, and these are guidelines intended to capture those conventions.


Identifiers
------------

In general, follow the guidelines in [Microsoft's capitalization conventions](https://docs.microsoft.com/en-us/dotnet/standard/design-guidelines/capitalization-conventions).  

Specifically use PascalCase (i.e. start with a capital letter) for namespaces and types,
including those introduced
with `structure`, `inductive`, classes, and `def`.  Use a leading lowercase letter
(camelCase) for other definitions including constructors and structure field names.

Indention
---------

Do not use tabs, when indenting use two spaces for indenting inside if statements and cases, e.g.,

```
def f : Nat → Nat
| i =>
  if i = 0 then
    1
  else
    i * f (i-1)
```

Use hanging `do`, e.g.,

```
def foo := do
  something;
  else
```

Rather than other styles such as

```
def foo :=
  do something;
     else
```

Structures
----------

structure fields are not indented and types are left aligned, e.g., 

```
structure NamedMD :=
(name   : String)
(values : List Nat)
```

When initializing structs with 3 or more fields, programmers should use named
parameter syntax rather than argument lists, and if all the assignments do not
fit on a single line uses aligned assignments with commas after each field
assignment, e.g.,

```
  { field1 := expr1,
    field2 := expr2,
    field3 := expr3,
  }
```
    

Match expressions
-----------------

Each case in a match has the underscore aligned with the match statement, .e.g.,

```
  match id with
  | Case1 => ...
  | Case2 => ...
```
