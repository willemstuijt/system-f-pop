module Tests (runTests, runExpr) where

import AST
import Check
import Parser

-- Some utilities to run the tests

data TestResult
  = Ok
  | OkTyped Type
  | ParseError String
  | TypeError
  | TypeErrorStr String
  deriving (Eq)

instance Show TestResult where
  show Ok = "Ok"
  show (OkTyped t) = "OkTyped " ++ show t
  show (ParseError msg) = "ParseError " ++ show msg
  show TypeError = "TypeError"
  show (TypeErrorStr err) = err

data TestOutput
  = Failed String
  | Passed
  deriving (Eq)

instance Show TestOutput where
  show (Failed err) = "Failed: " ++ err
  show Passed = "Passed"

resultsToOutput :: TestResult -> TestResult -> TestOutput
resultsToOutput (Ok) (Ok) = Passed
resultsToOutput (OkTyped _) (Ok) = Passed
resultsToOutput (OkTyped a) (OkTyped b) = if identity a b then Passed else Failed $ "got '" ++ (show a) ++ "', expected " ++ (show b)
resultsToOutput (ParseError _) (ParseError _) = Passed
resultsToOutput (TypeError) (TypeError) = Passed
resultsToOutput (TypeErrorStr _) (TypeError) = Passed
resultsToOutput (TypeErrorStr x) (TypeErrorStr y) | x == y = Passed
resultsToOutput result expected = Failed $ "got '" ++ (show result) ++ "', expected " ++ (show expected)

type Test = (String, TestResult)

-- Test cases for the typechecker
-- It is assumed that these tests will be run with the initial
-- defaultCtx that is declared in Main.hs

tests :: [Test]
tests =
  [ ("λ○x:Lin. (x, x)", TypeError), -- Using linear variable x twice
    ("λx:Lin. λy:Int. x", TypeError), -- Linear variable x in unrestricted lambda
    ("λx:Int. λy:Lin. x", TypeError), -- Unused linear variable y
    ("λ○x:Lin. λ○y:Lin. λ○z:Lin. (x, (y, z))", Ok), -- Nested linear lambdas with proper usage
    ("pack a:○ = Lin in λx:a. x : a -> a", Ok), -- Existential type with linear kind
    ("pack a:○ = Lin in λ○x:a. x : a -○ a", Ok), -- Existential type with linear kind
    ("pack a:○ = Lin in λ○x:a. x : a -> a", TypeError), -- Existential is an unrestricted lambda while expression is linear lambda
    ("λf:(Lin -○ Lin). λ○x:Lin. f x", Ok), -- Linear function application
    ("λf:(Int -○ Lin). λ○x:Int. (f x, f x)", TypeError), -- Linear function used twice
    ("λf:(Lin -> Lin). λx:Lin. f x", Ok), -- Unrestricted function with linear argument
    ("λf:(Int -> Int). λx:Lin. f 3", TypeError), -- Linear variable x is unused

    ("(ΛX:✱. λx:X. x) [Int]", Ok),
    ("(ΛX:✱. λx:X. x) [Lin]", TypeError), -- Cannot apply linear type to unrestricted forall
    ("((ΛX:✱. ΛY:✱. λx:X. λy:Y. (x, y)) [Int]) [Int]", Ok), -- Nested type abstractions and applications
    ("(ΛX:○. λx:X. λ○y:Lin. (x, y)) [Lin]", Ok), -- Linear type in type abstraction
    ("λ○x:Int. ΛY:✱. λy:Y. x", Ok), -- Type abstraction in linear context
    ("λ○x:Int. ΛY:○. λy:Y. x", TypeError), -- Unused linear variable y
    ("(ΛX:✱. λx:X. x) [Lin -> Lin]", Ok), -- Type application using a function type
    ("(ΛX:✱. λx:X. x) [Lin -○ Lin]", TypeError), -- Linear lambda is not of unrestricted kind
    ("(ΛX:○. λ○x:X. x) [Lin]", Ok), -- Linear kind in type abstraction and application
    ("λf:(∀X:✱. X -> X). (f [Int]) 3", Ok), -- Higher-order function with type abstraction
    ("λx:Lin. λf:(∀X:✱. X -> X). (f [Lin]) x", TypeError), -- Lin is not unrestricted
    ("((ΛX:✱. ΛY:○. λx:X. λ○y:Y. (x, y)) [Int]) [Lin]", Ok), -- Combining linear and unrestricted types in type abstractions
    ("λx:Lin. (λy:Int. y)", TypeError), -- Unused linear variable x
    ("λx:Lin. (λy:Int. x)", TypeError), -- Cannot use linear value inside unrestricted lambda
    ("ΛY:○. (λy:Y. y)", Ok), -- Can use linear value in unrestricted lambda as long as it is the argument itself
    ("(λf:(∀X:✱. X -> X). f) (ΛY:✱. λx:Y. x)", Ok),
    ("(λf:(∀X:✱. X -> X). f) (ΛY:○. λx:Y. x)", TypeError), -- Linear param to unrestricted param should fail
    ("(λf:(∀X:○. X -> X). f) (ΛY:✱. λx:Y. x)", Ok),
    ("(λ○f:(∀X:○. X -○ X). f) (ΛY:○. λ○x:Y. x)", Ok),
    ("λx:(Int, Int). (let (a, b, c) = x in (a, b, c))", TypeError), -- Destructure tuple with extra params
    ("λx:(Int, Int). (let (a, b) = x in (a, b))", Ok), -- Destructure tuple with right params
    ("λx:(Int, Int, Int). (let (a, b) = x in (a, b))", TypeError), -- Destructure tuple with less params

    ("(ΛA:○. ΛB:○. λx:A. λ○y:B. ΛG:○. λ○f:(A -○ B -○ G). ((f x) y))", Ok), -- (,) encoding from Figure 4.
    ("λx:Int. (((λx:Int. λ○y:Int. ΛG:○. λ○f:(Int -○ Int -○ G). ((f x) y)) x) x)", Ok), -- (,) encoding being used
    ("λx:Lin. (((λx:Lin. λ○y:Lin. ΛG:○. λ○f:(Lin -○ Lin -○ G). ((f x) y)) x) x)", TypeError), -- using linear variable x twice with (,) encoding
    ("let (x, y) = (1, 2) in (x, x)", Ok),

    ("λx:Lin. (pack a:✱ = Lin in x : a)", TypeError), -- Cannot pack a linear type as an unrestricted existential parameter

    ("λf:String. (\
    \  let handle = unsafeOpen f in \
    \    pack a:○ = UnsafeFH in \
    \      ( handle \
    \      , (λh:UnsafeFH. (unsafeRead h, h)) \
    \      , unsafeClose \
    \      ) : (a, a -> (Char, a), a -> ()) \
    \)", Ok), -- Example under Figure 1 typechecks correctly, I omitted the write function for brevity

    ("let open = (λf:String. (\
    \  let handle = unsafeOpen f in \
    \    pack a:○ = UnsafeFH in \
    \      ( handle \
    \      , (λh:UnsafeFH. (unsafeRead h, h)) \
    \      , unsafeClose \
    \      ) : (a, a -> (Char, a), a -> ()) \
    \)) in\
    \     unpack a, (h, read, close) = (open \"some file\") in\
    \       let (ch, h) = read h in\
    \         close h\
    \", Ok), -- Using the open function, reading and closing also works

    ("let open = (λf:String. (\
    \  let handle = unsafeOpen f in \
    \    pack a:○ = UnsafeFH in \
    \      ( handle \
    \      , (λh:UnsafeFH. (unsafeRead h, h)) \
    \      , unsafeClose \
    \      ) : (a, a -> (Char, a), a -> ()) \
    \)) in\
    \     unpack a, (h, read, close) = (open \"some file\") in\
    \       let (ch, h) = read h in\
    \         ch\
    \", TypeError) -- The linear file handle was not used so we get an error
  ]

runExpr :: Context -> String -> TestResult
runExpr ctx testInput = case parseSystemF testInput of
    Left err -> ParseError $ show err
    Right term -> case checkProgram ctx term of
        Left err -> TypeErrorStr err
        Right t -> OkTyped t

runTest :: Context -> Test -> TestOutput
runTest ctx (testInput, expected) = resultsToOutput (runExpr ctx testInput) expected

runTests :: Context -> [TestOutput]
runTests ctx = map (runTest ctx) tests
