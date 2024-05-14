# System F○ Type Checker

This project implements a type checker for System F○ based on the paper of Mazurak, Zhao, and Zdancewic[[1]](#1). Linear types are a feature in type systems where values must be used exactly once, providing a strong guarantee about resource usage and memory safety.

## Files Description

- `AST.hs`: Contains the data structures representing the abstract syntax tree, types and kinds.
- `Check.hs`: Implements the type checking algorithm, ensuring that the given program adheres to the rules of linear types in System F. This file has the most comments with a lot of references to the original paper.
- `Lexer.hs`: Includes the lexer, responsible for converting the source code into tokens that can be parsed.
- `Main.hs`: The main entry point of the program, handling command-line arguments.
- `Parser.hs`: Contains the parser, transforming a sequence of tokens into an AST.
- `Tests.hs`: A suite of tests to ensure the correctness of the type checker.

## How to Build and Run

This project uses Stack, a Haskell build tool. Below are the steps to build and run the type checker.

### Building the Project

1. Navigate to the project's root directory in your terminal.
2. Run the following command to build the project:

   ```sh
   stack build
   ```

This will compile the Haskell files and produce an executable.

### Running the Type Checker

After building the project, you can run the type checker with the following commands:

#### To run the tests
```sh
stack exec Linear test
```

#### To run the typechecker on a file, for example "test.fpop"
```sh
stack exec Linear test.fpop
```

## References
<a id="1">[1]</a> 
Mazurak, K., Zhao, J., & Zdancewic, S. (2010). Lightweight linear types in System F. In Proceedings of the 5th ACM SIGPLAN workshop on Types in language design and implementation (pp. 77-88).
