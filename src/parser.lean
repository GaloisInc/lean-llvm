import init.control.alternative
import init.control.applicative
import init.control.monad

import init.data.char


namespace Nat.
  def fromDigitsAux : List ℕ → ℕ → ℕ 
  | [] n := n
  | (d::ds) n := fromDigitsAux ds (n*10 + d).

  def fromDigits (ds:List ℕ) := fromDigitsAux ds 0.
end Nat.

structure parse (α:Type) := 
  (runParse :
     Π(z:Type),
       (List String → String → z)   /- global failure continuation -/ →
       (List String → String → z)   /- local failure continuation -/ →
       (α → List String → String → z) /- success continuation -/ →
       List String → String → z).

namespace parse.

instance functor : Functor parse :=
  { map := λa b f (m:parse a), parse.mk (λz kerr kfail k, 
              m.runParse z kerr kfail (λx, k (f x)))
  , mapConst := λa b x (m:parse b), parse.mk (λz kerr kfail k, 
              m.runParse z kerr kfail (λ_, k x))
  }.

instance hasPure : HasPure parse :=
  { pure := λa x, parse.mk (λz kerr kfail k, k x) }.

instance hasSeq : HasSeq parse :=
  { seq := λa b mf mx, parse.mk (λz kerr kfail k,
             mf.runParse z kerr kfail (λf,
             mx.runParse z kerr kfail (λx,
             k (f x))))
  }.

instance hasSeqLeft : HasSeqLeft parse :=
  { seqLeft := λa b mx my, parse.mk (λz kerr kfail k,
             mx.runParse z kerr kfail (λx,
             my.runParse z kerr kfail (λ_,
             k x)))
  }.

instance hasSeqRight : HasSeqRight parse :=
  { seqRight := λa b mx my, parse.mk (λz kerr kfail k,
             mx.runParse z kerr kfail (λ_,
             my.runParse z kerr kfail (λy,
             k y)))
  }.

instance hasBind : HasBind parse :=
  { bind := λa b mx mf, parse.mk (λz kerr kfail k,
              mx.runParse z kerr kfail (λx,
                (mf x).runParse z kerr kfail k))
  }.

instance alternative : Alternative parse :=
  { failure := λa, parse.mk (λz kerr kfail k, kfail)
  , orelse  := λa ma mb, parse.mk (λz kerr kfail k stk str,
      ma.runParse z kerr (λ_ _, mb.runParse z kerr kfail k stk str) k stk str)
  }.

instance applicative : Applicative parse := Applicative.mk _.
instance monad : Monad parse := Monad.mk _.

def run {α} (m:parse α) : String → (List String × String) ⊕ α :=
  m.runParse _
    (λstk str, Sum.inl (stk,str))
    (λstk str, Sum.inl (stk,str))
    (λx stk str, if str.isEmpty then Sum.inr x else Sum.inl (stk,str))
    [].

def describe {α} (msg:String) (m:parse α) : parse α :=
  parse.mk (λz kerr kfail k stk str,
    m.runParse z kerr kfail (λx _ str', k x stk str') (msg::stk) str).

def text (x:String) : parse String :=
  parse.mk (λz kerr kfail k stk str,
    if String.isPrefixOf x str then
      k x stk (String.drop str (x.length))
    else
      kfail (("expected string: " ++ x) :: stk) str).
 
def char (p:Char → Bool) : parse Char :=
  parse.mk (λz kerr kfail k stk str,
    let c := str.toSubstring.front in
    if ¬str.isEmpty ∧ p c then
      k c stk (String.drop str 1)
    else
      kfail stk str).

def chars (p:Char → Bool) : parse String :=
  parse.mk (λz kerr kfail k stk str,
    let str' := String.takeWhile str p in
    k str' stk (String.drop str (String.length str'))).

def digit : parse ℕ :=
  describe "digit" $ 
  do c <- char Char.isDigit,
     pure (c.val.toNat - ('0'.val.toNat))

def commit {α} (m:parse α) : parse α :=
  parse.mk (λz kerr _kfail k,
    m.runParse z kerr kerr k).

def delimit {α} (m:parse α) : parse α :=
  parse.mk (λz kerr kfail k,
    m.runParse z kfail kfail k)

def opt {α} (default:α) (m:parse α) : parse α :=
  parse.mk (λz kerr _kfail k stk str,
    m.runParse z kerr (λ_ _, k default stk str) k stk str).

def opt' {α} (m:parse α) : parse (Option α) :=
  opt none (some <$> m).

def choosePrefix {α} : List (String × parse α) → parse α :=
  delimit ∘ List.foldr (λb m, (text b.1 *> commit b.2) <|> m) failure.

partial def manyAux {α} (m:parse α) (z:Type) (someZ : z)
  : (List α → List String → String → z) → List String → String → z

| k stk str :=
   let kend := λ(_:List String) (_:String), k [] stk str in
   m.runParse z 
     kend
     kend
     (λx, manyAux (λxs, k (x::xs)))
     stk
     str.

def many {α} (m:parse α) : parse (List α) :=
  parse.mk (λz kerr _kfail, manyAux m z (kerr [] "")).

def manyOne {α} (m:parse α) : parse (α × List α) :=
  do x <- m,
     xs <- many m,
     pure (x,xs).

def manyOne' {α} (m:parse α) : parse (List α) :=
  do x <- m,
     xs <- many m,
     pure (x::xs).

def sepBy {α β} (m:parse α) (sep:parse β) : parse (List α) :=
  (List.cons <$> m <*> many (sep *> m)).

def nat : parse ℕ := 
  parse.describe "nat"
    (Nat.fromDigits <$> manyOne' digit).

def eof : parse Unit :=
  parse.mk (λz kerr kfail k stk str,
    if str.isEmpty then k () stk str else kfail ("Expected EOF"::stk) str).

end parse.
