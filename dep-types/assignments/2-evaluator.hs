module Main where

-- Declaring a newtype keeps us from confusing the two ways that
-- strings are used here: as messages to the user, and as names.
newtype Name = Name String
  deriving (Eq, Ord, Show)

-- The expressions are similar to previous arithmetic expressions, but
-- now they have functions and variables as well.
data Expr = Var Name
          | App Expr Expr
          | Lambda Name Expr
          | CstI Integer
          | Plus Expr Expr
  deriving (Eq, Show)

-- There are two values: closures, which are the values of functions,
-- and integers.
data Value = Closure Env Name Expr
           | IntegerVal Integer
  deriving (Eq, Show)

newtype Message = Message String
  deriving Show


-- The values of variables are looked up in an environment. This list
-- goes backwards: earlier entries take precedence over later
-- entries. In the environment
--   Env [(Name "x", IntegerVal 3), (Name "x", IntegerVal 5)]
-- the variable "x" has value 3.
newtype Env = Env [(Name, Value)]
  deriving (Eq, Show)

-- The initial environment is empty
initEnv :: Env
initEnv = Env []


extend :: Env -> Name -> Value -> Env
extend (Env env) x v = Env ((x, v) : env)

failure :: String -> Either Message a
failure msg = Left (Message msg)

lookupVar :: Env -> Name -> Either Message Value
lookupVar (Env []) x = failure ("Unbound: " ++ show x)
lookupVar (Env ((y, val) : env)) x
  | x == y = error "TODO"
  | otherwise = lookupVar (Env env) x



eval :: Env -> Expr -> Either Message Value
eval env (Var x) = lookupVar env x
eval env (App rator rand) =
  error "TODO"
eval env (Lambda x body) =
  error "TODO"
eval env (CstI i) =
  error "TODO"
eval env (Plus e1 e2) =
  error "TODO"


doApply :: Value -> Value -> Either Message Value
doApply (Closure env x body) arg =
  error "TODO"
doApply notFun arg =
  failure ("Not fun: " ++ show notFun)


doPlus :: Value -> Value -> Either Message Value
doPlus (IntegerVal i1) (IntegerVal i2) =
  error "TODO"
doPlus other1 other2 =
  failure ("One of these is not an integer: " ++
           show other1 ++ " " ++ show other2)

alphaEquiv :: Expr -> Expr -> Bool
alphaEquiv e1 e2 = helper 0 [] e1 [] e2
  where
    -- More cases are necessary in this function
    helper i xs (Var x) ys (Var y) =
      case (lookup x xs, lookup y ys) of
        (Nothing, Nothing) -> x == y
        (Just n, Just m) -> n == m
        _ -> False
    helper i xs (App f1 a1) ys (App f2 a2) =
      error "TODO"
    helper i xs (Lambda x e1) ys (Lambda y e2) =
      error "TODO"
    helper _ _ _ _ _ = False


---------------------------------------
-- Test code begins here.
---------------------------------------

define :: Env -> Name -> Expr -> Either Message Env
define env x e =
  do val <- eval env e
     return (extend env x val)


-- Church numerals are a representation of numbers as functions.
-- Each number takes a function and a start value as arguments.
-- Zero returns the start value, having applied the function 0 times.
-- A number n applies the function n times to the start value; this means
-- that 3 is λ f . λ x . f (f (f x)).
--
-- Due to shadowing, Church numerals are a nice way to test evaluators.
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
     return env2



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

testValIs :: String -> (Env -> Either Message Env) -> Expr -> Value -> IO ()
testValIs name setup expr wanted =
  do putStr (name ++ ": ")
     case setup initEnv of
       Left (Message err) -> error err
       Right env ->
         case eval env expr of
           Left (Message err) -> error err
           Right val ->
             if val == wanted
               then putStrLn "Success"
               else putStrLn "Failed"

testBoolIs name b wanted =
  do putStr (name ++ ": ")
     if b == wanted then putStrLn "Success" else putStrLn "Failed"

testTrue name b = testBoolIs name b True
testFalse name b = testBoolIs name b False


noSetup :: Env -> Either Message Env
noSetup env = Right env

main :: IO ()
main =
  do testValIs "identity" noSetup
       (Lambda (Name "x") (Var (Name "x")))
       (Closure initEnv (Name "x") (Var (Name "x")))
     testValIs "shadowing" noSetup
       (Lambda (Name "x") (Lambda (Name "x") (Lambda (Name "y") (App (Var (Name "y")) (Var (Name "x"))))))
       (Closure initEnv (Name "x") (Lambda (Name "x") (Lambda (Name "y") (App (Var (Name "y")) (Var (Name "x"))))))
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

