-- KolmoC Compilation Target for Bend
-- Compiles Bend programs to KolmoC syntax

module Target.KolmoC
  ( compile
  , CompileError(..)
  ) where

import Control.Exception (throw)
import Core.Show (BendException(..))
import Core.Type (Book(..), Error(..))
import qualified Data.Map as M

import Target.KolmoC.Type
import Target.KolmoC.Compile
import Target.KolmoC.Show

-- Re-export error type for API
type CompileError = KCompileError

-- Main compilation function
-- Takes a Bend Book and main function name, produces KolmoC source code
compile :: Book -> String -> String
compile book mainFQN =
  case compileBook book mainFQN of
    Left err -> throw (BendException $ CompilationError $ showError err)
    Right (kbook, mainNick) -> showKolmoC kbook mainNick

-- Format compilation errors
showError :: KCompileError -> String
showError err = case err of
  UnsupportedConstruct desc ->
    "Unsupported construct: " ++ desc ++ ". This feature is not available in the KolmoC backend."

  UnsupportedNumericType typ ->
    "Unsupported numeric type: " ++ typ ++ ". KolmoC only supports U32 integers."

  PatternMatchNotDesugared msg ->
    "Pattern match not desugared: " ++ msg ++ ". This is a compiler bug - pattern matches should be desugared before KolmoC compilation."

  IONotSupported msg ->
    "IO operations are not supported in the KolmoC backend: " ++ msg

  MetaVariableNotSupported msg ->
    "Meta variables are not supported in the KolmoC backend: " ++ msg

  ForkNotSupported msg ->
    "Fork constructs are not supported in the KolmoC backend: " ++ msg

  NumericConversionWarning msg val ->
    "Warning: " ++ msg ++ " (value: " ++ show val ++ ")"

  InvalidNick nick ->
    "Invalid nick: " ++ nick ++ ". Nicks must be 1-4 characters."

  UnknownReference ref ->
    "Unknown reference: " ++ ref

  DuplicateDefinition nick ->
    "Duplicate definition for nick: " ++ nick