{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall            #-}

module Ok where

-- Instructions:
--
-- Please add pairs to this implementation of untyped normalization.
--
--
-- In particular, your tasks are:
--  0. Add constructors for cons, car, and cdr to Expr
--  1. Identify the new neutral expressions, and add the corresponding
--     constructor(s) to Neutral
--  2. Identify the additional values. Add the corresponding
--     constructor(s) to Value
--  3. Extend eval to cover the new expressions, and implement helpers for
--     car and cdr. Your helpers should cover all values: the
--     "Non-exhaustive patterns" message should never occur.
--  4. Extend readBackValue and readBackNeutral for the extra constructors
--     from tasks 1 and 2
--  5. Extend alphaEquiv with the constructors from task 0
--  6. Write tests that check that the following equations are respected
--     by your implementation:
-- (car (cons a d)) = a
-- (cdr (cons a d)) = d
-- (cons a1 d1) = (cons a1 d1)
-- (car x) = (car x)
-- (cdr x) = (cdr x)
--     As an example, tests for the first equation could be written:
     -- testNormIs "(car (cons 2 4)) = 2" noSetup
     --   (First (Cons (CstI 2) (CstI 4)))
     --   (CstI 2)
     -- testNormIs "(car (cons a d)) = a" noSetup
     --   (Lambda (Name "a")
     --     (Lambda (Name "d")
     --      (First (Cons (Var (Name "a")) (Var (Name "d"))))))
     --   (Lambda (Name "a")
     --     (Lambda (Name "d")
     --      (Var (Name "a"))))

import Data.String

newtype Name = Name String
  deriving (Eq, Ord, Show, IsString)

newtype Message = Message String
  deriving (Eq, Ord, Show)

data Expr
  = Var Name
  | App Expr Expr
  | Cons Expr Expr
  | First Expr  -- "car" but that's an objectively stupid name
  | Second Expr -- "cdr" but that's an objectively stupid name
  | Lambda Name Expr
  | CstI Integer
  deriving (Eq, Show)

data Neutral
  = NVar Name
  | NApp Neutral Value
  | NFirst Neutral
  | NSecond Neutral
  deriving (Eq, Show)

data Value
  = VClosure Env Name Expr
  | VInt Integer
  | VPair Value Value
  | Neutral Neutral
  deriving (Eq, Show)

newtype Env = Env [(Name, Value)]
  deriving (Eq, Show)

envNames :: Env -> [Name]
envNames (Env env) = map fst env

initEnv :: Env
initEnv = Env []

extend :: Env -> Name -> Value -> Env
extend (Env env) x v = Env ((x, v) : env)

failure :: String -> Either Message a
failure message = Left (Message message)


lookupVar :: Env -> Name -> Either Message Value
lookupVar (Env [])               x =
  pure $ Neutral $ NVar x
  -- failure ("Unbound: " ++ show x)
lookupVar (Env ((y, val) : env)) x
  | x == y = pure val
  | otherwise = lookupVar (Env env) x

normalize :: Env -> Expr -> Either Message Expr
normalize env e = eval env e >>= readBackValue (envNames env)

eval :: Env -> Expr -> Either Message Value
eval env (Var x) = lookupVar env x
eval env (Cons x y) = VPair <$> eval env x <*> eval env y
eval env (First x) =
  eval env x >>= \case
    VPair a _ -> pure a
    Neutral n -> pure $ Neutral $ NFirst n
    _ -> failure "took first of something that wasn't a pair"
eval env (Second x) =
  eval env x >>= \case
    VPair _ b -> pure b
    Neutral n -> pure $ Neutral $ NSecond n
    _ -> failure "took second of something that wasn't a pair"
eval env (App rator rand) =
  do fun <- eval env rator
     arg <- eval env rand
     doApply fun arg
eval env (Lambda x body) =
  pure (VClosure env x body)
eval _ (CstI n) =
  pure (VInt n)

doApply :: Value -> Value -> Either Message Value
doApply (VClosure env x body) arg =
  eval (extend env x arg) body
doApply (Neutral ne) arg =
  pure (Neutral (NApp ne arg))
doApply other _ =
  failure $ "Not a function: " ++ show other

freshen :: [Name] -> Name -> Name
freshen used x
  | x `elem` used = freshen used (addTick x)
  | otherwise = x
  where addTick (Name y) = Name (y ++ "'")

readBackValue :: [Name] -> Value -> Either Message Expr
readBackValue used v@(VClosure _ x _) =
  do let y = freshen used x
     body <- doApply v $ Neutral $ NVar y
     bodyExpr <- readBackValue (y : used) body
     pure (Lambda y bodyExpr)
readBackValue _ (VInt i) = pure $ CstI i
readBackValue used (VPair a b) = Cons <$> readBackValue used a <*> readBackValue used b
readBackValue used (Neutral ne) =
  readBackNeutral used ne

readBackNeutral :: [Name] -> Neutral -> Either Message Expr
readBackNeutral _ (NVar x) = pure (Var x)
readBackNeutral used (NFirst n) = First <$> readBackNeutral used n
readBackNeutral used (NSecond n) = Second <$> readBackNeutral used n
readBackNeutral used (NApp ne v) =
  do rator <- readBackNeutral used ne
     rand <- readBackValue used v
     pure (App rator rand)


alphaEquiv :: Expr -> Expr -> Bool
alphaEquiv e1 e2 = helper 0 [] e1 [] e2
  where
    helper :: Integer -> [(Name, Integer)] -> Expr -> [(Name, Integer)] -> Expr -> Bool
    helper i xs (Var x) ys (Var y) =
      case (lookup x xs, lookup y ys) of
        (Nothing, Nothing) -> x == y
        (Just n, Just m) -> n == m
        _ -> False
    helper i xs (App f1 a1) ys (App f2 a2) =
      helper i xs f1 ys f2 && helper i xs a1 ys a2
    helper i xs (Lambda x e1) ys (Lambda y e2) =
      helper (i + 1) ((x, i) : xs) e1 ((y, i) : ys) e2
    helper i _ (CstI n) _ (CstI m) = n == m
    helper i xs (Cons a1 b1) ys (Cons a2 b2) =
      helper i xs a1 ys a2 && helper i xs b1 ys b2
    helper i xs (First a1) ys (First a2) =
      helper i xs a1 ys a2
    helper i xs (Second a1) ys (Second a2) =
      helper i xs a1 ys a2
    helper _ _ _ _ _ = False

---------------------------------------
-- Test code begins here.
---------------------------------------

define :: Env -> Name -> Expr -> Either Message Env
define env x e =
  do val <- eval env e
     pure (extend env x val)

-- Church numerals are a representation of numbers as functions.
-- Each number takes a function and a start value as arguments.
-- Zero returns the start value, having applied the function 0 times.
-- A number n applies the function n times to the start value; this means
-- that 3 is λ f . λ x . f (f (f x)).
--
-- Due to shadowing, Church numerals are a nice way to test normalizers.

defineChurchNums :: Env -> Either Message Env
defineChurchNums env =
  do env1 <- define env (Name "zero")
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



defineChurchAdd :: Env -> Either Message Env
defineChurchAdd env =
  define env (Name "+")
    (Lambda (Name "j")
      (Lambda (Name "k")
        (Lambda (Name "f")
          (Lambda (Name "x")
            (App (App (Var (Name "j")) (Var (Name "f")))
              (App (App (Var (Name "k")) (Var (Name "f")))
                (Var (Name "x"))))))))


toChurch :: Integer -> Expr
toChurch n
  | n <= 0 = Var (Name "zero")
  | otherwise = App (Var (Name "add1")) (toChurch (n - 1))

testNormIs :: String -> (Env -> Either Message Env) -> Expr -> Expr -> IO ()
testNormIs name setup expr wanted =
  do putStr (name ++ ": ")
     case setup initEnv of
       Left (Message err) -> error err
       Right env ->
         case normalize env expr of
           Left (Message err) -> error err
           Right norm
             | norm `alphaEquiv` wanted ->
               putStrLn "Success"
             | otherwise ->
               putStrLn "Failed"

testBoolIs name b wanted =
  do putStr (name ++ ": ")
     if b == wanted then putStrLn "Success" else putStrLn "Failed"

testTrue name b = testBoolIs name b True
testFalse name b = testBoolIs name b False


noSetup :: Env -> Either Message Env
noSetup env = Right env


main :: IO ()
main =
  do testNormIs "identity" noSetup
       (Lambda (Name "x") (Var (Name "x")))
       (Lambda (Name "x") (Var (Name "x")))
     testNormIs "shadowing" noSetup
       (Lambda (Name "x") (Lambda (Name "x") (Lambda (Name "y") (App (Var (Name "y")) (Var (Name "x"))))))
       (Lambda (Name "x") (Lambda (Name "x") (Lambda (Name "y") (App (Var (Name "y")) (Var (Name "x"))))))
     testNormIs "3" defineChurchNums
       (toChurch 3)
       (Lambda (Name "f")
         (Lambda (Name "x")
           (App (Var (Name "f"))
             (App (Var (Name "f"))
               (App (Var (Name "f"))
                 (Var (Name "x")))))))
     testNormIs "5" (\env -> do env' <- defineChurchNums env; defineChurchAdd env')
       (App (App (Var (Name "+")) (toChurch 3)) (toChurch 2))
       (Lambda (Name "f")
         (Lambda (Name "x")
           (App (Var (Name "f"))
             (App (Var (Name "f"))
               (App (Var (Name "f"))
                 (App (Var (Name "f"))
                  (App (Var (Name "f"))
                    (Var (Name "x")))))))))
     testNormIs "Capture-avoidance" noSetup
       (Lambda (Name "x")
         (App (Lambda (Name "y")
                (Lambda (Name "x")
                  (Var (Name "y"))))
           (Var (Name "x"))))
       (Lambda (Name "y")
         (Lambda (Name "z")
           (Var (Name "y"))))

     testNormIs "(car (cons 2 4)) = 2" noSetup
       (First (Cons (CstI 2) (CstI 4)))
       (CstI 2)
     testNormIs "(car (cons a d)) = a" noSetup
       (Lambda (Name "a")
         (Lambda (Name "d")
          (First (Cons (Var (Name "a")) (Var (Name "d"))))))
       (Lambda (Name "a")
         (Lambda (Name "d")
          (Var (Name "a"))))

     testNormIs "(cdr (cons 2 4)) = 2" noSetup
       (Second (Cons (CstI 2) (CstI 4)))
       (CstI 2)
     testNormIs "(cdr (cons a d)) = a" noSetup
       (Lambda (Name "a")
         (Lambda (Name "d")
          (Second (Cons (Var (Name "a")) (Var (Name "d"))))))
       (Lambda (Name "a")
         (Lambda (Name "d")
          (Var (Name "a"))))

     testNormIs "(cons a d) = (cons a d)" noSetup
        (Cons (Var (Name "a")) (Var (Name "d")))
        (Cons (Var (Name "a")) (Var (Name "d")))

     testNormIs "(car x) = (car x)" noSetup
        (First $ Var "x")
        (First $ Var "x")

     testNormIs "(snd x) = (snd x)" noSetup
        (Second $ Var "x")
        (Second $ Var "x")

     testNormIs "3 = 3" noSetup (CstI 3) (CstI 3)
     testNormIs "15 = 15" noSetup (CstI 15) (CstI 15)

