module Main (main) where

import Tests
import AST
import Check

import System.Environment

defaultCtx :: Context
-- defaultCtx = [ ("Int", TypeVarBind UnKind)
--             , ("Char", TypeVarBind UnKind)
--             , ("String", TypeVarBind UnKind)
--             , ("Lin", TypeVarBind LinKind)
--             , ("File", TypeVarBind LinKind)
--             , ("open", VarBind (FunType UnKind (TypeVar "String") (TypeVar "File")))
--             , ("read", VarBind (FunType UnKind (TypeVar "File") (TupleType [(TypeVar "Char"), (TypeVar "File")])))
--             , ("close", VarBind (FunType UnKind (TypeVar "File") (TupleType [])))]
defaultCtx = [ ("Int", TypeVarBind UnKind)
            , ("Char", TypeVarBind UnKind)
            , ("String", TypeVarBind UnKind)
            , ("Lin", TypeVarBind LinKind)
            , ("UnsafeFH", TypeVarBind UnKind)
            , ("unsafeOpen", VarBind (FunType UnKind (TypeVar "String") (TypeVar "UnsafeFH")))
            , ("unsafeRead", VarBind (FunType UnKind (TypeVar "UnsafeFH") (TypeVar "Char")))
            , ("unsafeClose", VarBind (FunType UnKind (TypeVar "UnsafeFH") (TupleType [])))]

main :: IO ()
main = do
    args <- getArgs
    case args of
        [filePath] ->
            if filePath == "test"
                then handleTest
                else do
                    content <- readFile filePath
                    print $ runExpr defaultCtx content
        _ -> putStrLn "Usage: program <filepath or test>"

handleTest :: IO ()
handleTest = do
    putStrLn "Running tests..."
    mapM_ print (runTests defaultCtx)
