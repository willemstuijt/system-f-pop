module AST (Kind (..), subK, Type (..), substitute, identity, typeToTerm, TypeTerm (..), Term (..)) where

import Data.List (intercalate)

-- This file contains Kinds, Types and the AST types.
-- It is mostly self explanatory so no comments are included
-- see Check.hs for the majority of comments

data Kind
  = UnKind
  | LinKind
  deriving (Eq)

instance Show Kind where
  show UnKind = "✱"
  show LinKind = "○"

subK :: Kind -> Kind -> Bool
subK (UnKind) (UnKind) = True
subK (UnKind) (LinKind) = False
subK (LinKind) (UnKind) = True
subK (LinKind) (LinKind) = True

data Type
  = TypeVar String
  | TupleType [Type]
  | FunType Kind Type Type
  | ForallType String Kind Type
  | ExistsType String Kind Type
  deriving (Eq)

instance Show Type where
  show (TypeVar x) = x
  show (TupleType ts) = "(" ++ (intercalate ", " (fmap show ts)) ++ ")"
  show (FunType UnKind a b) = (show a) ++ " -> " ++ (show b)
  show (FunType LinKind a b) = (show a) ++ " -○ " ++ (show b)
  show (ForallType x k t) = "∀" ++ x ++ ":" ++ (show k) ++ " " ++ (show t)
  show (ExistsType x k t) = "∃" ++ x ++ ":" ++ (show k) ++ " " ++ (show t)

substitute :: String -> Type -> Type -> Type
substitute x s (TypeVar y) = if x == y then s else TypeVar y
substitute x s (TupleType ts) = TupleType (fmap (substitute x s) ts)
substitute x s (FunType k t1 t2) = FunType k (substitute x s t1) (substitute x s t2)
substitute x s (ForallType y k t') = ForallType y k (substitute x s t')
substitute x s (ExistsType y k t') = ExistsType y k (substitute x s t')

identity :: Type -> Type -> Bool
identity (TypeVar a) (TypeVar b) = a == b
identity (TupleType as) (TupleType bs) = (length as == length bs) && and (fmap (\(a, b) -> identity a b) (zip as bs))
identity (FunType k1 a1 a2) (FunType k2 b1 b2) = subK k2 k1 && identity a1 b1 && identity a2 b2
identity (ForallType x k1 a) (ForallType y k2 b) = subK k2 k1 && identity (substitute x (TypeVar $ x ++ y ++ "!") a) (substitute y (TypeVar $ x ++ y ++ "!") b)
identity (ExistsType x k1 a) (ExistsType y k2 b) = subK k2 k1 && identity (substitute x (TypeVar $ x ++ y ++ "!") a) (substitute y (TypeVar $ x ++ y ++ "!") b)
identity _ _ = False

typeToTerm :: Type -> TypeTerm
typeToTerm (TypeVar x) = TypeVarTerm x
typeToTerm (TupleType ts) = TupleTerm (fmap typeToTerm ts)
typeToTerm (FunType k param result) = FunTerm k (typeToTerm param) (typeToTerm result)
typeToTerm (ForallType x k t) = ForallTerm x k (typeToTerm t)
typeToTerm (ExistsType x k t) = ExistsTerm x k (typeToTerm t)

data TypeTerm
  = TypeVarTerm String
  | TupleTerm [TypeTerm]
  | FunTerm Kind TypeTerm TypeTerm
  | ForallTerm String Kind TypeTerm
  | ExistsTerm String Kind TypeTerm
  deriving (Show, Eq)

data Term
  = Var String
  | StringLit String
  | NumberLit Integer
  | Abs Kind String TypeTerm Term
  | App Term Term
  | TyAbs String Kind Term
  | TyApp Term TypeTerm
  | Let String Term Term
  | Tuple [Term]
  | TupleLet [String] Term Term
  | Pack String Kind TypeTerm Term TypeTerm
  | Unpack String String Term Term
  | TupleUnpack String [String] Term Term
  deriving (Show, Eq)
