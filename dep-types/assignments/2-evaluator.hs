{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# OPTIONS_GHC -Wall                   #-}

module Main where

import Data.String
import Data.Bifunctor (second)

newtype Name = Name String
  deriving newtype (Eq, Ord, Show, IsString)

-- The expressions are similar to previous arithmetic expressions, but
-- now they have functions and variables as well.
data Expr a
  = Var a
  | App (Expr a) (Expr a)
  | Lambda a (Expr a)
  | CstI Integer
  | Plus (Expr a) (Expr a)
  deriving (Eq, Show, Functor)

-- There are two values: closures, which are the values of functions,
-- and integers.
data Value a
  = Closure (Env a) a (Expr a)
  | IntegerVal Integer
  deriving (Eq, Show, Functor)

newtype Message = Message String
  deriving Show

newtype Env a = Env [(a, Value a)]
  deriving stock (Functor)
  deriving newtype (Eq, Show, Semigroup, Monoid)

type ErrorM = Either Message


extend :: Env a -> a -> Value a -> Env a
extend (Env env) x v = Env ((x, v) : env)

failure :: String -> ErrorM a
failure = Left . Message

lookupVar :: (Eq a, Show a) => Env a -> a -> ErrorM (Value a)
lookupVar (Env []) x = failure $ "Unbound: " ++ show x
lookupVar (Env ((y, val) : env)) x
  | x == y = Right val
  | otherwise = lookupVar (Env env) x

asInt :: Value a -> ErrorM Integer
asInt (IntegerVal i) = pure i
asInt (Closure _ _ _) = failure "not an integer!"

asClosure :: Value a -> ErrorM (Env a, a, Expr a)
asClosure (IntegerVal _) = failure "not a lambda"
asClosure (Closure a b c) = pure (a, b, c)


eval :: (Eq a, Show a) => Env a -> Expr a -> ErrorM (Value a)
eval env (Var x) = lookupVar env x
eval env (App rator rand) = do
  (env', name, body) <- asClosure =<< eval env rator
  a <- eval env rand
  eval (extend env' name a) body
eval env (Lambda x body) =
  pure $ Closure env x body
eval _ (CstI i) = pure $ IntegerVal i
eval env (Plus e1 e2) = do
  v1 <- asInt =<< eval env e1
  v2 <- asInt =<< eval env e2
  pure $ IntegerVal $ v1 + v2

data Bound a
  = Free a
  | Bound Int
  deriving (Eq, Ord, Show)

debruijnify :: forall a. Eq a => Expr a -> Expr (Bound a)
debruijnify = go mempty
  where
    go :: [(a, Int)] -> Expr a -> Expr (Bound a)
    go env (Var n)      = Var $ maybe (Free n) (Bound) $ lookup n env
    go env (App f a)    = App (go env f) (go env a)
    go env (Lambda n b) = Lambda (Bound 0) (go ((n, 0) : fmap (second (+ 1)) env) b)
    go env (Plus e1 e2) = Plus (go env e1) (go env e2)
    go _   (CstI i)     = CstI i


alphaEquiv :: Eq a => Expr a -> Expr a -> Bool
alphaEquiv a b = debruijnify a == debruijnify b


---------------------------------------
-- Test code begins here.
---------------------------------------

define :: (Eq a, Show a) => Env a -> a -> Expr a -> ErrorM (Env a)
define env x e = do
  val <- eval env e
  pure $ extend env x val


-- Church numerals are a representation of numbers as functions.
-- Each number takes a function and a start value as arguments.
-- Zero returns the start value, having applied the function 0 times.
-- A number n applies the function n times to the start value; this means
-- that 3 is λ f . λ x . f (f (f x)).
--
-- Due to shadowing, Church numerals are a nice way to test evaluators.
defineChurchNums :: Env Name -> ErrorM (Env Name)
defineChurchNums env = do
  env1 <- define env (Name "zero")
               (Lambda (Name "f")
                (Lambda (Name "x")
                 (Var (Name "x"))))
  env2 <- define env1 (Name "add1")
               (Lambda (Name "n")
                (Lambda (Name "f")
                 (Lambda (Name "x")
                  (App (Var (Name "f"))
                   (App (App (Var (Name "n")) (Var (Name "f")))
                    (Var (Name "x")))))))
  pure env2



defineChurchAdd :: Env Name -> ErrorM (Env Name)
defineChurchAdd env =
  define env (Name "+")
    (Lambda (Name "j")
      (Lambda (Name "k")
        (Lambda (Name "f")
          (Lambda (Name "x")
            (App (App (Var (Name "j")) (Var (Name "f")))
              (App (App (Var (Name "k")) (Var (Name "f")))
                (Var (Name "x"))))))))

toChurch :: Integer -> Expr Name
toChurch n
  | n <= 0 = Var (Name "zero")
  | otherwise = App (Var (Name "add1")) (toChurch (n - 1))

testValIs :: String -> (Env Name -> ErrorM (Env Name)) -> Expr Name -> Value Name -> IO ()
testValIs name setup expr wanted =
  do putStr (name ++ ": ")
     case setup mempty of
       Left (Message err) -> error err
       Right env ->
         case eval env expr of
           Left (Message err) -> error err
           Right val ->
             if val == wanted
               then putStrLn "Success"
               else putStrLn "Failed"

testBoolIs :: Eq a => String -> a -> a -> IO ()
testBoolIs name b wanted =
  do putStr (name ++ ": ")
     if b == wanted then putStrLn "Success" else putStrLn "Failed"

testTrue :: String -> Bool -> IO ()
testTrue name b = testBoolIs name b True

testFalse :: String -> Bool -> IO ()
testFalse name b = testBoolIs name b False


noSetup :: Env a -> ErrorM (Env a)
noSetup env = Right env

main :: IO ()
main =
  do testValIs "identity" noSetup
       (Lambda (Name "x") (Var (Name "x")))
       (Closure mempty (Name "x") (Var (Name "x")))
     testValIs "shadowing" noSetup
       (Lambda (Name "x") (Lambda (Name "x") (Lambda (Name "y") (App (Var (Name "y")) (Var (Name "x"))))))
       (Closure mempty (Name "x") (Lambda (Name "x") (Lambda (Name "y") (App (Var (Name "y")) (Var (Name "x"))))))
     testValIs "Church 3" defineChurchNums
       (toChurch 3)
       (Closure (Env [ ( Name "n"
                       , Closure
                           (Env [ ( Name "n"
                                  , Closure
                                      (Env [ ( Name "n"
                                             , Closure (Env []) (Name "f") (Lambda (Name "x") (Var (Name "x")))
                                             )
                                           , ( Name "zero"
                                             , Closure (Env []) (Name "f") (Lambda (Name "x") (Var (Name "x")))
                                             )
                                           ])
                                      (Name "f")
                                      (Lambda (Name "x")
                                        (App (Var (Name "f"))
                                          (App (App (Var (Name "n")) (Var (Name "f")))
                                            (Var (Name "x"))))))
                                ,(Name "zero",Closure (Env []) (Name "f") (Lambda (Name "x") (Var (Name "x"))))
                                ])
                           (Name "f")
                           (Lambda (Name "x") (App (Var (Name "f")) (App (App (Var (Name "n")) (Var (Name "f"))) (Var (Name "x"))))))
                     , ( Name "zero"
                       , Closure (Env []) (Name "f")
                           (Lambda (Name "x")
                             (Var (Name "x"))))
                     ])
        (Name "f")
        (Lambda (Name "x")
         (App (Var (Name "f"))
          (App (App (Var (Name "n")) (Var (Name "f")))
           (Var (Name "x"))))))
     testValIs "Real 3" defineChurchNums
       (App (App (toChurch 3)
             (Lambda (Name "n")
              (Plus (Var (Name "n"))
               (CstI 1))))
        (CstI 0))
       (IntegerVal 3)
     testValIs "Scope testing" noSetup
       (App (Lambda (Name "x")
             (App (App (Lambda (Name "x")
                        (Lambda (Name "y")
                         (Var (Name "x"))))
                   (CstI 1))
              (CstI 2)))
        (CstI 3))
       (IntegerVal 1)
     testTrue "Free and equal"
       (alphaEquiv (Var (Name "x")) (Var (Name "x")))
     testFalse "Free and inequal"
       (alphaEquiv (Var (Name "x")) (Var (Name "y")))
     testFalse "One bound, one free"
       (alphaEquiv (Lambda (Name "x") (Var (Name "x")))
                   (Lambda (Name "y") (Var (Name "x"))))
     testTrue "Bound and equivalent"
       (alphaEquiv (Lambda (Name "x") (Var (Name "x")))
                   (Lambda (Name "y") (Var (Name "y"))))
     testTrue "Three is three"
       (alphaEquiv (Lambda (Name "f")
                     (Lambda (Name "x")
                       (App (Var (Name "f"))
                         (App (Var (Name "f"))
                           (App (Var (Name "f"))
                             (Var (Name "x")))))))
                   (Lambda (Name "x")
                     (Lambda (Name "f")
                       (App (Var (Name "x"))
                         (App (Var (Name "x"))
                           (App (Var (Name "x"))
                             (Var (Name "f"))))))))
     testTrue "Arithmetic expression equivalence"
       (alphaEquiv (Lambda (Name "x")
                    (Plus (CstI 1)
                     (Plus (Var (Name "x"))
                      (Var (Name "x")))))
                   (Lambda (Name "y")
                    (Plus (CstI 1)
                     (Plus (Var (Name "y"))
                      (Var (Name "y"))))))
     testFalse "Arithmetic expression inequivalence"
       (alphaEquiv (Lambda (Name "x")
                    (Plus (CstI 5)
                     (Plus (Var (Name "x"))
                      (Var (Name "x")))))
                   (Lambda (Name "y")
                    (Plus (CstI 1)
                     (Plus (Var (Name "y"))
                      (Var (Name "y"))))))

