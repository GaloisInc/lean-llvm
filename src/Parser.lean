import Init.Control.Alternative
import Init.Control.Applicative
import Init.Control.Monad

import Init.Data.Char


namespace Nat.
  def fromDigitsAux : List Nat → Nat → Nat
  | [],    n => n
  | d::ds, n => fromDigitsAux ds (n*10 + d).

  def fromDigits (ds:List Nat) := fromDigitsAux ds 0.
end Nat.

structure parse (α:Type) :=
  (runParse :
     ∀(z:Type),
       (List String → String → z)   /- global failure continuation -/ →
       (List String → String → z)   /- local failure continuation -/ →
       (α → List String → String → z) /- success continuation -/ →
       List String → String → z).

namespace parse.

instance monad : Monad parse :=
  { bind := λa b mx mf => parse.mk (λz kerr kfail k =>
              mx.runParse z kerr kfail (λx =>
                (mf x).runParse z kerr kfail k))
  , pure := λa x => parse.mk (λz kerr kfail k => k x)
  }.

instance alternative : Alternative parse :=
  { failure := λa => parse.mk (λz kerr kfail k => kfail)
  , orelse  := λa ma mb => parse.mk (λz kerr kfail k stk str =>
      ma.runParse z kerr (λ_ _ => mb.runParse z kerr kfail k stk str) k stk str)
  }.

def run {α} (m:parse α) : String → Sum (List String × String) α :=
  m.runParse _
    (λstk str => Sum.inl (stk,str))
    (λstk str => Sum.inl (stk,str))
    (λx stk str => if str.isEmpty then Sum.inr x else Sum.inl (stk,str))
    [].

def describe {α} (msg:String) (m:parse α) : parse α :=
  parse.mk (λz kerr kfail k stk str =>
    m.runParse z kerr kfail (λx _ str' => k x stk str') (msg::stk) str).

def text (x:String) : parse String :=
  parse.mk (λz kerr kfail k stk str =>
    if String.isPrefixOf x str then
      k x stk (String.drop str (x.length))
    else
      kfail (("expected string: " ++ x) :: stk) str).

def char (p:Char → Bool) : parse Char :=
  parse.mk (λz kerr kfail k stk str =>
    let c := str.toSubstring.front;
    if ¬str.isEmpty ∧ p c then
      k c stk (String.drop str 1)
    else
      kfail stk str).

def chars (p:Char → Bool) : parse String :=
  parse.mk (λz kerr kfail k stk str =>
    let str' := String.takeWhile str p;
    k str' stk (String.drop str (String.length str'))).

def digit : parse Nat :=
  describe "digit" $
  do c <- char Char.isDigit;
     pure (c.val.toNat - ('0'.val.toNat))

def commit {α} (m:parse α) : parse α :=
  parse.mk (λz kerr _kfail k =>
    m.runParse z kerr kerr k).

def delimit {α} (m:parse α) : parse α :=
  parse.mk (λz kerr kfail k =>
    m.runParse z kfail kfail k)

def opt {α} (default:α) (m:parse α) : parse α :=
  parse.mk (λz kerr _kfail k stk str =>
    m.runParse z kerr (λ_ _ => k default stk str) k stk str).

def opt' {α} (m:parse α) : parse (Option α) :=
  opt none (some <$> m).

def choosePrefix {α} : List (String × parse α) → parse α :=
  delimit ∘ List.foldr (λb m => (do _ <- text b.1; commit b.2) <|> m) failure.

partial def manyAux {α} (m:parse α) (z:Type) (someZ : z)
  : (List α → List String → String → z) → List String → String → z

| k, stk, str =>
   let kend := λ(_:List String) (_:String) => k [] stk str;
   m.runParse z
     kend
     kend
     (λx => manyAux (λxs => k (x::xs)))
     stk
     str.

def many {α} (m:parse α) : parse (List α) :=
  parse.mk (λz kerr _kfail => manyAux m z (kerr [] "")).

def manyOne {α} (m:parse α) : parse (α × List α) :=
  do x <- m;
     xs <- many m;
     pure (x,xs).

def manyOne' {α} (m:parse α) : parse (List α) :=
  do x <- m;
     xs <- many m;
     pure (x::xs).

def sepBy {α β} (m:parse α) (sep:parse β) : parse (List α) :=
  (List.cons <$> m <*> many (do _ <- sep; m)).

def nat : parse Nat :=
  parse.describe "nat"
    (Nat.fromDigits <$> manyOne' digit).

def textThen {α} (strLit:String) (m:parse α) : parse α :=
do _ <- text strLit; m

def eof : parse Unit :=
  parse.mk (λz kerr kfail k stk str =>
    if str.isEmpty then k () stk str else kfail ("Expected EOF"::stk) str).

end parse.
