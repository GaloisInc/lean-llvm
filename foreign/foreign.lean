-- This file contains concepts relevant from control.io, foreign, and foreign.c
-- mdoules for implementing a C foreign-function interface in Lean.

import system.io

universe u

namespace io

--- @bracket acquire release between@ aquires a resource, run the code
-- in between and then releases the resource.
constant bracket {α} {β} {γ}  : io α → (α → io β) → (α → io γ) → io γ

end io

namespace foreign

constant ptr : Type → Type

constant ptr.null {α:Type} : ptr α

constant ptr.byte_add {α β:Type} : ptr α → ℤ → ptr β

class storable (α:Type) :=
(memsize   : ℕ)
(alignment : ℕ)
(peek : ptr α → io α)
(poke : ptr α → α → io unit)

open storable


constant ptr.storable (α:Type) : storable (ptr α)

noncomputable
def ptr.elem_add {α:Type} [storable α] (p:ptr α) (i:ℤ) : ptr α :=
  p.byte_add (memsize α * i)

noncomputable
def ptr.elem_inc {α:Type} [storable α] (p:ptr α) : ptr α := p.byte_add (memsize α)

noncomputable
def ptr.elem_dec {α:Type} [storable α] (p:ptr α) : ptr α := p.byte_add (int.neg (memsize α))

/-- Allocate a pointer wot hte given number of bytes and free it when done. -/
constant alloca_bytes {α} {̱{β} (sz:ℕ) (f : ptr α → io β) : io β

/-- Allocate a pointer to a value and free it when done. -/
def alloca {α} {̱{β} [h:storable α] (f : ptr α → io β) : io β :=
  alloca_bytes (memsize α) f

/-- Allocate a pointer to an array of values and free it when done. -/
def alloca_array {α} {̱{β} [h:storable α] (n:ℕ) (f : ptr α → io β) : io β :=
  alloca_bytes (n * memsize α) f

/-- Convert an array of the given length into a list of values. -/
def peek_array.imp {α} {̱[h:storable α] : ℕ → ptr α → list α → io (list α)
| 0 p l := pure l
| (succ n) p l :=
  h ← peek (ptr.elem_dec p),
  peek_array.imp n (ptr.elem_dec p) (h::l)

/-- Read elements out of an array of the given length, and return list. -/
def peek_list {α} {̱[h:storable α] (n:ℕ) (p : ptr α) : io (list α) :=
  peek_array.imp n (p.elem_add n)

/-- Convert an array of the given length into a list of values. -/
def poke_list {α} {̱[h:storable α] : ptr α → list α → io unit
| p [] := pure ()
| p (h::r) := poke p h, poke_list p.elem_inc r

-- C-specific types

namespace c

/-- char in C -/
def cchar : Type := fin 256
constant cchar.storable : storable cchar

/-- int in C -/
constant cint : Type
constant cint.storable : storable cint

/-- long in C -/
constant clong : Type
constant clong.storable : storable clong

/-- size_t -/
constant csize : Type
constant csize.storable : storable csize

@[reducible]
def cstring := ptr cchar

/-- Read a string with the given number of characters. -/
constant cstring.utf8.peeklen : cstring → csize → io string

/-- Read a null-terminated string -/
constant cstring.utf8.peek : cstring → io string

/-- Construct a pointer to a null terminated string from the string. -/
constant string.withcstring.utf8 {α} : string → (ptr cstring → io α) → io α

-- Note. We likely want other encodings (e.g. ASCII with no unicode).

end c

end foreign
