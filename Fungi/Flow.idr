{- A type level algorithm for composable unification. Everything 
 - here is public export so that the type checker can reduce them. 
 - Since everything here used must be public export, several things 
 - from prelude, base, etc., are redefined. Proofs are provided 
 - along the way for sanity checks if at Flow e, the datatype defined 
 - within this module, is a way to provide the labels of edges of 
 - Fungi.Algebraic.DynGraph "types" and to enforce the semantics of 
 - Fungi.Algebraic.DynGraph at the type level. 
 -}
module Fungi.Flow

namespace So

  public export
  data So : Bool -> Type where
    Oh : So True

  public export
  choose : (b : Bool) -> Either (So b) (So (not b))
  choose False = Right Oh
  choose True  = Left Oh

namespace List

  public export
  replicate : Nat -> a -> List a
  replicate 0     _ = Nil
  replicate (S k) x = x :: replicate k x

  public export
  unit : Nat -> List (Maybe a)
  unit n = replicate n Nothing

  namespace Replicate

    public export
    prf : (a : Type) -> (x : a) -> (n : Nat) -> length (replicate n x) === n
    prf a x 0     = Refl
    prf a x (S k) = cong S (prf a x k)

  public export
  data Unification : Eq e => List (Maybe e) -> List (Maybe e) -> Type where
    Success : Eq e => Unification (the (List (Maybe e)) []) (the (List (Maybe e)) [])
    LeftTooShort : Eq e
                => (0 y : Maybe e)
                -> (0 ys : List (Maybe e))
                -> Unification (the (List (Maybe e)) []) (y :: ys)
    RightTooShort : Eq e 
                 => (0 x : Maybe e)
                 -> (0 xs : List (Maybe e)) 
                 -> Unification (x :: xs) (the (List (Maybe e)) [])
    TrivialMatch : Eq e 
                => {0 xs : List (Maybe e)}
                -> {0 ys : List (Maybe e)}
                -> Unification xs ys
                -> Unification (Nothing :: xs) (Nothing :: ys) 
    LeftSubst : Eq e
             => (y : e)
             -> Unification xs ys
             -> Unification (Nothing :: xs) (Just y :: ys)
    RightSubst : Eq e
              => (x : e)
              -> Unification xs ys
              -> Unification (Just x :: xs) (Nothing :: ys)
    Match : Eq e 
         => {0 y : e}
         -> (x : e)
         -> {auto 0 prf : So (x == y)}
         -> Unification xs ys
         -> Unification (Just x :: xs) (Just y :: ys)
    NoMatch : Eq e
           => (0 x : e)
           -> (0 y : e)
           -> (0 prf : So (not (x == y)))
           -> Unification (Just x :: xs) (Just y :: ys)

  public export
  unification : Eq e => (xs : List (Maybe e)) -> (ys : List (Maybe e)) -> Unification xs ys
  unification [] [] = Success
  unification [] (x :: xs) = LeftTooShort x xs
  unification (x :: xs) [] = RightTooShort x xs
  unification (Nothing :: xs) (Nothing :: ys) = TrivialMatch (unification xs ys)
  unification (Nothing :: xs) ((Just x) :: ys) = LeftSubst x (unification xs ys)
  unification ((Just x) :: xs) (Nothing :: ys) = RightSubst x (unification xs ys)
  unification ((Just x) :: xs) ((Just y) :: ys) = case choose (x == y) of
                                                       Left p => Match x (unification xs ys)
                                                       Right p => NoMatch x y p
          

  ||| A proof that the Unification of xs and ys
  ||| was successful.  
  public export 
  data Unifies : Eq e 
              => {xs : List (Maybe e)} 
              -> {ys : List (Maybe e)} 
              -> Unification xs ys 
              -> Type where
    TheSuccess : Eq e 
              => Unifies (the (Unification (the (List (Maybe e)) []) (the (List (Maybe e)) [])) Success)
    TheTrivialMatch : Eq e 
                   => {0 xs : List (Maybe e)}
                   -> {0 ys : List (Maybe e)}
                   -> {0 u : Unification xs ys}
                   -> Unifies u
                   -> Unifies (TrivialMatch u)
    TheLeftSubst : Eq e 
                => {0 xs : List (Maybe e)}
                -> {0 ys : List (Maybe e)}
                -> {0 u : Unification xs ys}
                -> (y : e)
                -> Unifies u  
                -> Unifies (LeftSubst y u)
    TheRightSubst : Eq e 
                 => {0 xs : List (Maybe e)}
                 -> {0 ys : List (Maybe e)}
                 -> {0 u : Unification xs ys}
                 -> (x : e)
                 -> Unifies u 
                 -> Unifies (RightSubst x u)
    TheMatch : Eq e 
            => (x : e)
            -> {0 y : e}
            -> {0 xs : List (Maybe e)}
            -> {0 ys : List (Maybe e)}
            -> {0 u : Unification xs ys}
            -> {0 prf : So (x == y)}
            -> Unifies u
            -> Unifies (Match {y = y} {prf = prf} x u)

  namespace Ununified

    public export
    noMatch : Eq e 
           => (0 x : e)
           -> (0 y : e)
           -> (0 p : So (not (x == y)))
           -> Not (Unifies (NoMatch x y p))
    noMatch _ _ _ TheSuccess impossible
    noMatch _ _ _ (TheTrivialMatch z) impossible
    noMatch _ _ _ (TheLeftSubst z w) impossible
    noMatch _ _ _ (TheRightSubst z w) impossible
    noMatch _ _ _ (TheMatch z w) impossible

    public export
    leftTooShort : Eq e
                => (0 y : Maybe e)
                -> (0 ys : List (Maybe e))
                -> Not (Unifies (LeftTooShort y ys))
    leftTooShort _ _ TheSuccess impossible
    leftTooShort _ _ (TheTrivialMatch x) impossible
    leftTooShort _ _ (TheLeftSubst x z) impossible
    leftTooShort _ _ (TheRightSubst x z) impossible
    leftTooShort _ _ (TheMatch x z) impossible

    public export
    rightTooShort : Eq e
                 => (0 x : Maybe e)
                 -> (0 xs : List (Maybe e))
                 -> Not (Unifies (RightTooShort x xs))
    rightTooShort _ _ TheSuccess impossible
    rightTooShort _ _ (TheTrivialMatch y) impossible
    rightTooShort _ _ (TheLeftSubst y z) impossible
    rightTooShort _ _ (TheRightSubst y z) impossible
    rightTooShort _ _ (TheMatch y z) impossible

    public export
    ununifiesRecTrivial : Eq e 
                       => {0 xs : List (Maybe e)}
                       -> {0 ys : List (Maybe e)}
                       -> {0 u : Unification xs ys}
                       -> (Unifies u -> Void) 
                       -> Unifies (TrivialMatch u) 
                       -> Void
    ununifiesRecTrivial f (TheTrivialMatch x) = f x

    public export
    ununifiesRecLeftSubst : Eq e 
                         => {0 xs : List (Maybe e)}
                         -> {0 ys : List (Maybe e)}
                         -> {0 u : Unification xs ys}
                         -> (Unifies u -> Void) 
                         -> Unifies (LeftSubst y u) 
                         -> Void
    ununifiesRecLeftSubst f (TheLeftSubst y z) = f z

    public export
    ununifiesRecRightSubst : Eq e 
                          => {0 xs : List (Maybe e)}
                          -> {0 ys : List (Maybe e)}
                          -> {0 u : Unification xs ys}
                          -> (Unifies u -> Void) 
                          -> Unifies (RightSubst x u) 
                          -> Void
    ununifiesRecRightSubst f (TheRightSubst x z) = f z

    public export
    ununifiesRecMatch : Eq e 
                     => {0 xs : List (Maybe e)}
                     -> {0 ys : List (Maybe e)}
                     -> {0 u : Unification xs ys}
                     -> {0 x : e}
                     -> {0 y : e}
                     -> {0 prf : So (x == y)}
                     -> (Unifies u -> Void) 
                     -> Unifies (Match {y = y} {prf = prf} x u) 
                     -> Void
    ununifiesRecMatch f (TheMatch x w) = f w

  public export
  unifies : Eq e 
         => {0 xs : List (Maybe e)} 
         -> {0 ys : List (Maybe e)}
         -> (u : Unification xs ys)
         -> Dec (Unifies u)
  unifies Success = Yes TheSuccess
  unifies (LeftTooShort y zs) = No (leftTooShort y zs)
  unifies (RightTooShort x zs) = No (rightTooShort x zs)
  unifies (TrivialMatch x) = case unifies x of 
                                  Yes p => Yes (TheTrivialMatch p)
                                  No p => No (ununifiesRecTrivial p)
  unifies (LeftSubst y x) = case unifies x of
                                 Yes p => Yes (TheLeftSubst y p)
                                 No p => No (ununifiesRecLeftSubst p)
  unifies (RightSubst x y) = case unifies y of 
                                  Yes p => Yes (TheRightSubst x p)
                                  No p => No (ununifiesRecRightSubst p)
  unifies (Match x y) = case unifies y of 
                             Yes p => Yes (TheMatch x p)
                             No p => No (ununifiesRecMatch p)
  unifies (NoMatch x y prf) = No (noMatch x y prf)

  namespace Unifies

    public export
    unifyRecTrivial : Eq e 
                   => {0 xs : List (Maybe e)} 
                   -> {0 ys : List (Maybe e)} 
                   -> {0 u : Unification xs ys}
                   -> Unifies (TrivialMatch u) 
                   -> Unifies u
    unifyRecTrivial (TheTrivialMatch x) = x

    public export
    unifyRecLeftSubst : Eq e 
                     => {0 xs : List (Maybe e)} 
                     -> {0 ys : List (Maybe e)} 
                     -> {0 u : Unification xs ys} 
                     -> Unifies (LeftSubst y u)
                     -> Unifies u
    unifyRecLeftSubst (TheLeftSubst y z) = z

    public export
    unifyRecRightSubst : Eq e 
                      => {0 xs : List (Maybe e)} 
                      -> {0 ys : List (Maybe e)} 
                      -> {0 u : Unification xs ys}
                      -> Unifies (RightSubst x u) 
                      -> Unifies u
    unifyRecRightSubst (TheRightSubst x z) = z

    public export
    unifyRecMatch : Eq e 
                 => {0 xs : List (Maybe e)} 
                 -> {0 ys : List (Maybe e)} 
                 -> {0 u : Unification xs ys}
                 -> {0 x : e}
                 -> {0 y : e}
                 -> {0 prf : So (x == y)}
                 -> Unifies (Match {y = y} {prf = prf} x u) 
                 -> Unifies u
    unifyRecMatch (TheMatch x w) = w

  namespace Unification

    public export
    leftUnit : Eq e
            => (xs : List (Maybe e))
            -> Unifies (unification (List.unit (length xs)) xs)
    leftUnit [] = TheSuccess
    leftUnit (Nothing :: xs) = TheTrivialMatch (leftUnit xs)
    leftUnit ((Just x) :: xs) = TheLeftSubst x (leftUnit xs)

    public export
    rightUnit : Eq e
             => (xs : List (Maybe e))
             -> Unifies (unification xs (List.unit (length xs)))
    rightUnit [] = TheSuccess
    rightUnit (Nothing :: xs) = TheTrivialMatch (rightUnit xs)
    rightUnit ((Just x) :: xs) = TheRightSubst x (rightUnit xs)

  public export
  unify : Eq e 
       => {0 xs : List (Maybe e)} 
       -> {0 ys : List (Maybe e)} 
       -> (u : Unification xs ys)
       -> {auto 0 prf : Unifies u}
       -> List (Maybe e)
  unify Success = []
  unify (LeftTooShort _ _) impossible
  unify (RightTooShort _ _) impossible
  unify (TrivialMatch x) = Nothing :: unify {prf = unifyRecTrivial prf} x
  unify (LeftSubst y x) = Just y :: unify {prf = unifyRecLeftSubst prf} x
  unify (RightSubst x y) = Just x :: unify {prf = unifyRecRightSubst prf} y
  unify (Match x y) = Just x :: unify {prf = unifyRecMatch prf} y
  unify (NoMatch _ _ _) impossible

  namespace Unify

    public export
    leftUnit : Eq e 
            => (xs : List (Maybe e)) 
            -> unify {prf = Unification.leftUnit xs} (unification (List.unit (length xs)) xs) === xs 
    leftUnit [] = Refl
    leftUnit (Nothing :: xs) = cong (Nothing ::) (leftUnit xs)
    leftUnit ((Just x) :: xs) = cong (Just x ::) (leftUnit xs)

    public export
    rightUnit : Eq e
             => (xs : List (Maybe e))
             -> unify {prf = Unification.rightUnit xs} (unification xs (List.unit (length xs))) === xs
    rightUnit [] = Refl
    rightUnit (Nothing :: xs) = cong (Nothing ::) (rightUnit xs)
    rightUnit ((Just x) :: xs) = cong (Just x ::) (rightUnit xs)

public export
data Result : Eq e => List (Maybe e) -> List (Maybe e) -> Type where
  Ok : Eq e
    => {0 xs : List (Maybe e)} 
    -> {0 ys : List (Maybe e)} 
    -> {0 u : Unification xs ys}
    -> {auto 0 prf : Unifies u}
    -> List (Maybe e)
    -> Result xs ys
  Error : Eq e
       => {0 xs : List (Maybe e)} 
       -> {0 ys : List (Maybe e)} 
       -> {0 u : Unification xs ys}
       -> {auto 0 prf : Not (Unifies u)}
       -> Result xs ys

public export
data Flow : Type -> Type where
  MkFlow : Eq e
        => (xs : List (Maybe e))
        -> ((ys : List (Maybe e)) -> Result xs ys)
        -> Flow e

