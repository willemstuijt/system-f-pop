module Check (checkProgram, Binding (..), Context) where

import AST

-- Context and its utilities

-- In the paper they use 2 different contexts:
-- - Gamma for unrestricted variables and type variables
-- - Delta for linear variables

-- I decided to combine both contexts in my implementation because
-- it made the implementation a bit simpler since unrestricted variables
-- can also be used as linear variables.
-- To check if a variable is linear we simply check its kind with the kindOf function.

type Context = [(String, Binding)]

-- VarBind: A variable binding
-- UsedVarBind: A VarBind whose type was linear and was already used by an expression.
--             we could have simply deleted the variable from the Context but I decided to replace
--             it with UsedVarBind instead to provide better error messages.
-- ForbiddenVarBind: Used for the [T-Lam] typing rule in Figure-3 to prevent using linear variables
--                   when the kind of the lambda is unrestricted. Before checking the body of the
--                   lambda we mark all linear variables as ForbiddenVarBind in the context to
--                   satisfy the ∆=·∨κ=◦ condition.
-- TypeVarBind: A type variable binding

data Binding = VarBind Type | UsedVarBind | ForbiddenVarBind Type | TypeVarBind Kind
  deriving (Show, Eq)

-- Some utilities, should be self explanatory

replaceFirst :: (Eq k) => k -> v -> [(k, v)] -> [(k, v)]
replaceFirst _ _ [] = []
replaceFirst key newVal ((k, v) : xs)
  | key == k = (k, newVal) : xs
  | otherwise = (k, v) : replaceFirst key newVal xs

removeFirst :: [a] -> [a]
removeFirst [] = []
removeFirst (_ : xs) = xs

-- These functions are used to replace (VarBind t) bindings where t has a linear kind with ForbiddenVarBind
-- the reason for this has already been explained above. The Int is used as a count so that we can restore
-- the same number of replaced variables after checking the function body.

hideLinears :: Context -> (Context, Int)
hideLinears ((k, VarBind t) : xs) = case kindOf xs t of
  (Just LinKind) -> ((k, ForbiddenVarBind t) : xs', n + 1)
  _ -> ((k, VarBind t) : xs', n)
  where
    (xs', n) = hideLinears xs
hideLinears (x : xs) = (x : xs', n)
  where
    (xs', n) = hideLinears xs
hideLinears [] = ([], 0)

showLinears :: Context -> Int -> Context
showLinears ctx 0 = ctx
showLinears ((k, ForbiddenVarBind t) : xs) n = (k, VarBind t) : showLinears xs (n - 1)
showLinears (x : xs) n = x : showLinears xs n
showLinears [] _ = []

-- Utilities to flatten lists of maybes and eithers
maybeList :: [Maybe a] -> Maybe [a]
maybeList (m : ms) = let xs = maybeList ms in
  case m of
    Just x -> fmap (\v -> (x : v)) xs
    Nothing -> Nothing
maybeList [] = Just []

eitherList :: [Either l r] -> Either l [r]
eitherList (m : ms) = let xs = eitherList ms in
  case m of
    Right x -> fmap (\v -> (x : v)) xs
    Left v -> Left v
eitherList [] = Right []

-- Returns the kind of a type given the Context
-- satisfies the kinding rules in Figure 3, page 4
kindOf :: Context -> Type -> Maybe Kind
kindOf ctx (TypeVar a) = case lookup a ctx of
  Just (TypeVarBind k) -> Just k
  _ -> Nothing
kindOf ctx (TupleType ts) = case maybeList (fmap (kindOf ctx) ts) of
  Just ks -> if (or (fmap (\k -> k == LinKind) ks))
    then Just LinKind
    else Just UnKind
  Nothing -> Nothing
kindOf _ (FunType k _ _) = Just k
kindOf ctx (ForallType x k t) = kindOf ((x, TypeVarBind k) : ctx) t
kindOf ctx (ExistsType x k t) = kindOf ((x, TypeVarBind k) : ctx) t

-- Given a type term and context, this function returns the type if it's well formed
checkTypeTerm :: Context -> TypeTerm -> Either String Type
checkTypeTerm ctx (TypeVarTerm x) = case lookup x ctx of
  Just (TypeVarBind _) -> Right $ TypeVar x
  _ -> Left $ "Unknown type variable: " ++ x
checkTypeTerm ctx (TupleTerm ts) = do
  ts' <- eitherList $ fmap (checkTypeTerm ctx) ts
  return $ TupleType ts'
checkTypeTerm ctx (FunTerm k p r) = do
  p' <- checkTypeTerm ctx p
  r' <- checkTypeTerm ctx r
  return $ FunType k p' r'
checkTypeTerm ctx (ForallTerm x k term) =
  case lookup x ctx of
    -- According to the typing rules in Figure 3 we should not allow
    -- binding of type variables when the name is already used in the context
    Just (TypeVarBind _) -> Left $ "Already declared type var: " ++ x
    _ -> do
      let ctx' = (x, TypeVarBind k) : ctx
      typ <- checkTypeTerm ctx' term
      return $ ForallType x k typ
checkTypeTerm ctx (ExistsTerm x k term) =
  case lookup x ctx of
    Just (TypeVarBind _) -> Left $ "Already declared type var: " ++ x
    _ -> do
      let ctx' = (x, TypeVarBind k) : ctx
      typ <- checkTypeTerm ctx' term
      return $ ExistsType x k typ

-- Main type-checking function. Takes a term and a context and returns the type of the term if it's well typed
-- as well as the Context to be used in future checkTerm calls. The context contains the updated state of linear
-- variables so they cannot be used twice.
-- Comments starting with square brackets are referencing the typing rules
-- of the paper found in Figures 3 and 7.
checkTerm :: Context -> Term -> Either String (Type, Context)
-- These weren't part of the paper but are nice to have
checkTerm ctx (StringLit _) = return (TypeVar "String", ctx)
checkTerm ctx (NumberLit _) = return (TypeVar "Int", ctx)

-- [T-LVar], [T-UVar] since this implementation deviates a bit from the paper
-- by combining both contexts into a single context the typing rules are a bit
-- different. But the purpose is the same. When we use a linear variable we replace
-- it with a UsedVarBind which will trigger an error the next time it is used. By
-- returning the context in checkTerm we ensure that the following expressions
-- to be checked will use the updated context, thus satisfying Contraction.
-- We also provide a nicer error when a linear variable is used within an unrestricted lambda.
checkTerm ctx (Var x) = case lookup x ctx of
  Just (VarBind t) -> case kindOf ctx t of
    Just UnKind -> Right (t, ctx)
    Just LinKind -> Right (t, replaceFirst x UsedVarBind ctx)
    _ -> Left $ "Unknown kind of type: " ++ show t
  Just UsedVarBind -> Left $ "Reused linear variable: " ++ x
  Just (ForbiddenVarBind _) -> Left $ "Cannot use linear variable '" ++ x ++ "' in unrestricted lambda"
  _ -> Left $ "Unknown variable: " ++ x
-- [T-Lam] we first check the parameter type, then we check the function body
-- and if the parameter is linear we return an error if it was used to satisfy Weakening.
-- To prevent linear variables from being used in the body of an unrestricted function we
-- call hideLinears on the context before checking the body of the unrestricted function.
-- The actual implementation is in checkBindings, which was refactored to reuse the logic in let bindings
checkTerm ctx (Abs k x tyT t) = do
  tyT' <- checkTypeTerm ctx tyT
  (t', ctx') <- checkBindings ctx k [(x, tyT')] t
  return $ (FunType k tyT' t', ctx')
-- [T-App] we check the function and its argument
-- to ensure that linear values are not used twice we pass the
-- returned context from checking fun which has all used linear variables marked as UsedVarBind
-- then we simply make sure the function is of type function and we check if the argument is compatible
checkTerm ctx (App t1 t2) = do
  (fun, ctx') <- checkTerm ctx t1
  (arg, ctx'') <- checkTerm ctx' t2
  case fun of
    FunType _ param result ->
      if identity arg param
        then return (result, ctx'')
        else Left "Type mismatch"
    nonFun -> Left $ "Non-function in application " ++ show nonFun
-- [T-TLam] checks that the name to be used for the type is not already in the context
-- then we add the new type binding to the context and check the term with it
-- we then remove the binding before returning
checkTerm ctx (TyAbs x kind t) = case lookup x ctx of
  Just _ -> Left $ "Already declared type var: " ++ x
  _ -> do
    let ctx' = (x, TypeVarBind kind) : ctx
    (tyT, ctx'') <- checkTerm ctx' t
    return $ (ForallType x kind tyT, removeFirst ctx'')
-- [T-TApp] checks the type of the expresssion which must be a ForallType
-- then checks the type of the type argument, the types must have the same kind as shown in the paper
-- if everything matches then we simply substitute
checkTerm ctx (TyApp t tyT) = do
  (t', ctx') <- checkTerm ctx t
  tyT' <- checkTypeTerm ctx' tyT
  case t' of
    ForallType x k allT -> case kindOf ctx' tyT' of
      Just k' ->
        if subK k k'
          then return (substitute x tyT' allT, ctx')
          else Left $ "Expected a type of kind " ++ show k
      _ -> Left $ "Unknown kind of type " ++ show tyT'
    _ -> Left "Non-polymorphic type in type application"

-- Lets aren't part of System F○, but I implemented them anyways
-- to facilitate writing examples, they are based on the Encodings
-- in Figure 4
checkTerm ctx (Let x v t) = do
  (v', ctx') <- checkTerm ctx v
  checkBindings ctx' LinKind [(x, v')] t
-- Tuples implement the extensions to System F○ shown in Figure 7.
checkTerm ctx (Tuple ts) = do
  (ts', ctx') <- checkTerms ctx ts
  return (TupleType ts', ctx')
-- Same as let but destructures tuples, this is necessary to interact
-- with tuples with linear elements since projections would violate linearity
checkTerm ctx (TupleLet ns v t) = do
  (v', ctx') <- checkTerm ctx v
  case v' of
    TupleType ts | (length ns == length ts) -> checkBindings ctx' LinKind (zip ns ts) t
    TupleType _ -> Left $ "Cannot destructure '" ++ show v' ++ "', mismatch in number of params"
    nonTuple -> Left $ "Cannot destructure '" ++ show nonTuple ++ "', not a tuple"

-- Existential types are added so that the example for the abstracted unsafe file
-- operations can be implemented for demonstration, their typing rules are not
-- explicitly in the paper.
checkTerm ctx (Pack a k t e t2) = case lookup a ctx of
  Just _ -> Left $ "Already declared type var: " ++ a
  _ -> do
    t' <- checkTypeTerm ctx t
    tk <- maybeToEither "Unkown kind" (kindOf ctx t')
    if not $ subK k tk
      then Left $ "Cannot pack a linear type '" ++ show t' ++ "' as an unrestricted existential parameter"
      else do
        let ctx' = (a, TypeVarBind k) : ctx
        (e', ctx'') <- checkTerm ctx' e
        t2' <- checkTypeTerm ctx'' t2
        let sub = substitute a t' t2'
        let eSub = substitute a t' e'
        if identity eSub sub
          then return $ (ExistsType a k t2', removeFirst ctx'')
          else Left $ "Term '" ++ show e' ++ "' does not match '" ++ show sub ++ "'"
checkTerm ctx (Unpack a x e e2) = do
  (e', ctx') <- checkTerm ctx e
  case e' of
    ExistsType a' k t -> do
      let t' = substitute a' (TypeVar a) t
      let ctx'' = (a, TypeVarBind k) : ctx'
      (res, ctx''') <- checkBindings ctx'' LinKind [(x, t')] e2
      return (res, removeFirst ctx''')
    _ -> Left "Non-existential type in unpack"
-- Same as unpack but also destructures a tuple, just syntax sugar
checkTerm ctx (TupleUnpack a xs e e2) = do
  (e', ctx') <- checkTerm ctx e
  case e' of
    ExistsType a' k t -> do
      let t' = substitute a' (TypeVar a) t
      let ctx'' = (a, TypeVarBind k) : ctx'
      case t' of
        TupleType ts | (length xs == length ts) -> do
          (res, ctx''') <- checkBindings ctx'' LinKind (zip xs ts) e2
          return (res, removeFirst ctx''')
        TupleType _ -> Left $ "Cannot destructure '" ++ show t' ++ "', mismatch in number of params"
        nonTuple -> Left $ "Cannot destructure '" ++ show nonTuple ++ "', not a tuple"
    _ -> Left "Non-existential type in unpack"

checkTerms :: Context -> [Term] -> Either String ([Type], Context)
checkTerms ctx (t:ts) = do
  (t', ctx') <- checkTerm ctx t
  (ts', ctx'') <- checkTerms ctx' ts
  Right (t' : ts', ctx'')
checkTerms ctx [] = Right ([], ctx)

-- Helper function
maybeToEither :: e -> Maybe a -> Either e a
maybeToEither _ (Just x) = Right x
maybeToEither e Nothing  = Left e

-- Checks if the defined variable was used
checkUsed :: Context -> [(String, Type)] -> Either String ()
checkUsed ctx ((name, varTyp):xs) = case kindOf ctx varTyp of
  Just LinKind -> case lookup name ctx of
    Just (VarBind _) -> Left $ "Linear variable '" ++ name ++ "' was not used"
    _ -> checkUsed ctx xs
  _ -> checkUsed ctx xs
checkUsed _ [] = return ()

-- Typechecks the bindings of variables, used for lambdas and let expressions
checkBindings :: Context -> Kind -> [(String, Type)] -> Term -> Either String (Type, Context)
checkBindings ctx k vars t = do
  case k of
    UnKind -> do
      let (ctx', n) = hideLinears ctx
      (t', ctx'') <- checkTerm (prepend vars ctx') t
      let ctx''' = showLinears ctx'' n
      _ <- checkUsed ctx''' vars
      return $ (t', removeFirst ctx''')
    LinKind -> do
      let ctx' = prepend vars ctx
      (t', ctx'') <- checkTerm ctx' t
      _ <- checkUsed ctx'' vars
      return $ (t', removeFirst ctx'')
  where
    prepend ((vname, vtype):xs) ctx2 = (vname, VarBind vtype) : (prepend xs ctx2)
    prepend [] ctx2 = ctx2

-- Helper function that gets rid of the resulting Context
checkProgram :: Context -> Term -> Either String Type
checkProgram ctx t = fmap (\(typ, _) -> typ) $ checkTerm ctx t
