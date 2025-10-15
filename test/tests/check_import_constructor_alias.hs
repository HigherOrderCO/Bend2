{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
import Tests/color as Color

def identity(c: Color::Color) -> Color::Color:
  match c:
    case @Color::Red:
      @Color::Red
    case @Color::Green:
      @Color::Green
    case @Color::Blue:
      @Color::Blue

def main : Color::Color =
  identity(@Color::Green)

def is_red(c: Color::Color) -> Bool:
  match c:
    case @Color::Red:
      True
    case _:
      False

def is_green(c: Color::Color) -> Bool:
  match c:
    case @Color::Green:
      True
    case _:
      False

assert True == is_red(identity(@Color::Red)) : Bool
assert True == is_green(identity(@Color::Green)) : Bool
assert True == is_green(main) : Bool
"""

color_bend :: String
color_bend = """
type Color:
  case @Red:
  case @Green:
  case @Blue:
"""

main :: IO ()
main = do
  projectDir <- findProjectRoot
  let cmd = "(cd BendRoot && cabal run -v0 bend --project-dir=" ++ show projectDir ++ " -- main.bend)"
  test cmd
    [ ("BendRoot/main.bend", main_bend)
    , ("BendRoot/Tests/color.bend", color_bend)
    ]
    "constructor names respect import alias rewriting"
    $ \_ err -> assert (err == "")
