module Main where

-- First, read and understand the type checker and implementation of typed NbE
-- 1. Add a unit type with the following grammar:
--
--   e ::= ...
--       | sole
--
--   t ::= ...
--       | Trivial
--
--   and the following rules:
--
--   ---------------- [TrivI]
--    sole ⇐ Trivial
--
--       e : Trivial
--   --------------------- [Triv-η]
--     sole ≡ e : Trivial
--
-- Paste the names of the rules next to the code that implements them in comments.
--
-- Hint: First add type and expression constructors, then add a value
-- constructor, then update the type checker and evaluator.
--
-- 2. What should the normal for be for
--    Ann (Lambda (Name "x") (Var (Name "x"))) (Arr Trivial Trivial) ?
--    Write your answer here, and add it as a test: Lambda (Name "x") Sole
--
-- 3. What should the normal for be for
--    Ann (Lambda (Name "x") (Var (Name "x"))) (Arr Nat Nat) ?
--    Write your answer here: Lambda (Name "x") (Var (Name "x"))
--
-- 4. What should the normal for be for
--    Ann (Lambda (Name "x") (Var (Name "x"))) (Arr (Arr Nat Nat) (Arr Nat Nat)) ?
--    Write your answer here: Lambda (Name "f") $ Lambda (Name "x") $ App (Var (Name "f")) (Var (Name "x"))
--
-- 5. What should the normal for be for
--    Ann (Lambda (Name "x") (Var (Name "x"))) (Arr (Arr Nat Trivial) (Arr Nat Trivial)) ?
--    Write your answer here, and add it as a test: Lambda (Name "f") $ Lambda (Name "x") $ Sole
--
-- Optional bonus problem: Using the implementation of rec-List as a
-- model, add rec-Nat to the language.

data Ty = Nat | Arr Ty Ty | List Ty | Trivial
  deriving (Eq, Show)

newtype Msg = Msg String
  deriving Show

newtype Name = Name String
  deriving (Eq, Show)

newtype Context = Context [(Name, Ty)]

initCtx = Context []

newtype Env = Env [(Name, Value)]

initEnv = Env []

extendEnv :: Env -> Name -> Value -> Env
extendEnv (Env env) x v = Env ((x, v) : env)

data Expr = Var Name | App Expr Expr | Lambda Name Expr
          | Zero | Add1 Expr
          | Nil | ListCons Expr Expr | RecList Ty Expr Expr Expr
          | Ann Expr Ty
          | Sole
  deriving Show

lookupVar (Context []) x = failure ("Var not found" ++ show x)
lookupVar (Context ((y, t) : ctx)) x
  | x == y = return t
  | otherwise = lookupVar (Context ctx) x

extend :: Context -> Name -> Ty -> Context
extend (Context ctx) x t = Context ((x, t) : ctx)

failure :: String -> Either Msg a
failure msg = Left (Msg msg)


synth :: Context -> Expr -> Either Msg Ty
synth ctx (Var x) = lookupVar ctx x
synth ctx (Ann e t) =
  do check ctx e t
     return t
synth ctx (App rator rand) =
  do t <- synth ctx rator
     case t of
       Arr a b ->
         do check ctx rand a
            return b
       other ->
         failure ("Expected a function, got a " ++ show other)
synth ctx (RecList t tgt base step) =
  do tgtTy <- synth ctx tgt
     case tgtTy of
       List e ->
         do check ctx base t
            check ctx step (Arr e (Arr (List e) (Arr t t)))
            return t
       other ->
         failure ("Target of recList must be a list")
synth ctx other =
  failure ("Can't synth for " ++ show other)

check :: Context -> Expr -> Ty -> Either Msg ()
check ctx Zero t =
  case t of
    Nat -> return ()
    other -> failure ("zero expected Nat but got " ++ show other)
check ctx (Add1 n) t =
  case t of
    Nat -> check ctx n Nat
    other -> failure ("add1 expected Nat but got " ++ show other)
check ctx (Lambda x body) t =
  case t of
    Arr a b ->
      check (extend ctx x a) body b
    other ->
      failure ("Lambda needs a function type but got " ++ show other)
check ctx Sole t = do -- [TrivI]
  case t of
    Trivial -> return ()
    other ->
      failure ("sole needs a trivial type but got " ++ show other)
check ctx Nil t =
  case t of
    List e -> return ()
    other ->
      failure ("nil needs a list type but got " ++ show other)
check ctx (ListCons hd tl) t =
  case t of
    List e ->
      do check ctx hd e
         check ctx tl (List e)
    other ->
      failure (":: needs a list type but got " ++ show other)
check ctx e t =
  do t' <- synth ctx e
     if t' == t
       then return ()
       else failure (show t' ++ " /= " ++ show t)


data Neutral = NVar Name | NApp Neutral Norm | NRecList Neutral Norm Norm

data Norm = Norm Ty Value

data Value = VClosure Env Name Expr
           | VZero | VAdd1 Value
           | VNil | VListCons Value Value
           | VNeutral Ty Neutral
           | VSole

evalVar :: Env -> Name -> Value
evalVar (Env []) x = error ("No value for " ++ show x)
evalVar (Env ((y, v) : env)) x
  | x == y    = v
  | otherwise = evalVar (Env env) x

eval :: Env -> Expr -> Value
eval env Sole = VSole
eval env (Var x) = evalVar env x
eval env (Lambda x body) = VClosure env x body
eval env (App rator rand) = doApply (eval env rator) (eval env rand)
eval env Zero = VZero
eval env (Add1 k) = VAdd1 (eval env k)
eval env Nil = VNil
eval env (ListCons e es) = VListCons (eval env e) (eval env es)
eval env (RecList ty tgt base step) = doRecList ty (eval env tgt) (eval env base) (eval env step)
eval env (Ann e _) = eval env e

doApply :: Value -> Value -> Value
doApply (VClosure env x body)        arg = eval (extendEnv env x arg) body
doApply (VNeutral (Arr dom ran) neu) arg = VNeutral ran (NApp neu (Norm dom arg))

doRecList :: Ty -> Value -> Value -> Value -> Value
doRecList ty VNil base step =
  base
doRecList ty (VListCons v vs) base step =
  doApply (doApply (doApply step v) vs) (doRecList ty vs base step)
doRecList ty (VNeutral (List e) neu) base step =
  VNeutral ty (NRecList neu (Norm ty base) (Norm (Arr e (Arr (List e) (Arr ty ty))) step))

freshen :: [Name] -> Name -> Name
freshen used x
  | elem x used = freshen used (nextName x)
  | otherwise   = x
  where
    nextName (Name y) = Name (y ++ "'")

getArgName :: Value -> Name
getArgName (VClosure _ x _) = x
getArgName _ = Name "x"

readBack :: [Name] -> Ty -> Value -> Expr
readBack used Trivial _ = Sole -- [Triv-η]
readBack used Nat VZero =
  Zero
readBack used Nat (VAdd1 n) =
  Add1 (readBack used Nat n)
readBack used (List e) VNil =
  Nil
readBack used (List e) (VListCons v vs) =
  ListCons (readBack used e v) (readBack used (List e) vs)
readBack used (Arr dom ran) v =
  let x = freshen used (getArgName v)
  in Lambda x (readBack (x : used) ran (doApply v (VNeutral dom (NVar x))))
readBack used t (VNeutral t' neu) =
  if t == t'
    then readBackNeutral used neu
    else error "Internal error: types that should match don't"

readBackNeutral :: [Name] -> Neutral -> Expr
readBackNeutral used (NVar x) =
  Var x
readBackNeutral used (NApp neu (Norm t arg)) =
  App (readBackNeutral used neu) (readBack used t arg)
readBackNeutral used (NRecList neu (Norm bt base) (Norm st step)) =
  RecList bt (readBackNeutral used neu) (readBack used bt base) (readBack used st step)


normalize :: Expr -> Either Msg Expr
normalize e =
  do ty <- synth initCtx e
     let v = eval initEnv e
     return (readBack [] ty v)

alphaEquiv :: Expr -> Expr -> Bool
alphaEquiv e1 e2 = helper 0 [] e1 [] e2
  where
    helper i xs (Var x) ys (Var y) =
      case (lookup x xs, lookup y ys) of
        (Nothing, Nothing) -> x == y
        (Just i, Just j) -> i == j
        _ -> False
    helper i xs Sole ys Sole = True
    helper i xs (Lambda x b1) ys (Lambda y b2) =
      helper (i + 1) ((x, i) : xs) b1 ((y, i) : ys) b2
    helper i xs (App fun1 arg1) ys (App fun2 arg2) =
      helper i xs fun1 ys fun2 && helper i xs arg1 ys arg2
    helper _ _ Zero _ Zero = True
    helper i xs (Add1 j) ys (Add1 k) = helper i xs j ys k
    helper _ _ Nil _ Nil = True
    helper i xs (ListCons e1 es1) ys (ListCons e2 es2) =
      helper i xs e1 ys e2 && helper i xs es1 ys es2
    helper i xs (RecList t1 tgt1 b1 s1) ys (RecList t2 tgt2 b2 s2) =
      t1 == t2 &&
      helper i xs tgt1 ys tgt2 &&
      helper i xs b1   ys b2   &&
      helper i xs s1   ys s2


---------------------------------------------------------------------------

testNorm :: String -> Expr -> Expr -> IO ()
testNorm name input norm =
  do putStr (name ++ ": ")
     case normalize input of
       Left msg -> error (show msg)
       Right e' -> do
         if alphaEquiv norm e'
           then putStrLn "Success!"
           else putStrLn "Failed..."

main = do
  testNorm "Identity, Nat -> Nat"
    (Ann (Lambda (Name "f") (Var (Name "f"))) (Arr Nat Nat))
    (Lambda (Name "f") (Var (Name "f")))
  testNorm "Identity, (Nat -> Nat) -> Nat -> Nat"
    (Ann (Lambda (Name "f") (Var (Name "f"))) (Arr (Arr Nat Nat) (Arr Nat Nat)))
    (Lambda (Name "f") (Lambda (Name "x") (App (Var (Name "f")) (Var (Name "x")))))
  testNorm "Append"
    (Ann (Lambda (Name "xs") (Lambda (Name "ys") (RecList (List Nat) (Var (Name "xs")) (Var (Name "ys")) (Lambda (Name "z") (Lambda (Name "_") (Lambda (Name "so-far") (ListCons (Var (Name "z")) (Var (Name "so-far"))))))))) (Arr (List Nat) (Arr (List Nat) (List Nat))))
    (Lambda (Name "xs") (Lambda (Name "ys") (RecList (List Nat) (Var (Name "xs")) (Var (Name "ys")) (Lambda (Name "z") (Lambda (Name "_") (Lambda (Name "so-far") (ListCons (Var (Name "z")) (Var (Name "so-far")))))))))
  testNorm "Append (:: 1 (:: 2 nil))"
    (App (Ann (Lambda (Name "xs") (Lambda (Name "ys") (RecList (List Nat) (Var (Name "xs")) (Var (Name "ys")) (Lambda (Name "z") (Lambda (Name "_") (Lambda (Name "so-far") (ListCons (Var (Name "z")) (Var (Name "so-far"))))))))) (Arr (List Nat) (Arr (List Nat) (List Nat)))) (ListCons (Add1 Zero) (ListCons (Add1 (Add1 Zero)) Nil)))
    (Lambda (Name "ys") (ListCons (Add1 Zero) (ListCons (Add1 (Add1 Zero)) (Var (Name "ys")))))

  testNorm
     "Length of nat lists"
     ( Ann
         ( Lambda
             (Name "xs")
             ( RecList
                 Nat
                 (Var (Name "xs"))
                 Zero
                 (Lambda (Name "hd") (Lambda (Name "_") (Lambda (Name "len") (Add1 (Var (Name "len"))))))))
         (Arr (List Nat) Nat))
     ( Lambda
         (Name "xs")
         ( RecList
             Nat
             (Var (Name "xs"))
             Zero
             (Lambda (Name "hd") (Lambda (Name "_") (Lambda (Name "len") (Add1 (Var (Name "len"))))))))


  testNorm
     "Test 2"
     (Ann (Lambda (Name "x") $ Var $ Name "x") $ Arr Trivial Trivial)
     (Lambda (Name "x") Sole)

  testNorm
     "Test 3"
     (Ann (Lambda (Name "x") (Var (Name "x"))) (Arr Nat Nat) )
     (Lambda (Name "x") (Var (Name "x")))

  testNorm
     "Test 4"
     (Ann (Lambda (Name "x") (Var (Name "x"))) (Arr (Arr Nat Nat) (Arr Nat Nat)) )
     (Lambda (Name "f") $ Lambda (Name "x") $ App (Var (Name "f")) (Var (Name "x")))


  testNorm
     "Test 5"
     (Ann (Lambda (Name "x") (Var (Name "x"))) (Arr (Arr Nat Trivial) (Arr Nat Trivial)))
     (Lambda (Name "f") $ Lambda (Name "x") $ Sole)





