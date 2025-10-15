# Bend2 - Work in Progress

Bend2 is the upcoming update of Bend - a high-level language that runs on GPUs -
introducing several new features and QOL improvements.

**NOTE: this project is a WORK IN PROGRESS. You're here before the launch. The
features described below are in development. Bend2 will launch when everything
described in this README is implemented.**

## Features

### SupGen - a powerful "Algorithm & Proof Miner"

After Bend's original release, I got involved in a research project, aiming to
create the most powerful synthesizer in the world - highly inspired by Idris2's
incredible [type-driven synthesis](https://www.youtube.com/watch?v=E7uSsL8r_mU).
The result of this work, SupGen, is now integrated in Bend2, making its compiler
capable of generating algorithms, instantly, without AI models. Check the demo:

```
TODO - record a demo (:
```

### Beyond GPUs - Target Everything™

Bend became popular for being the first programming language with first-class
functions, recursion and object allocation - i.e., a true high-level language
like Python and JavaScript - to compile and run on the GPUs. On Bend2, this
feature has been improved to cover more NVIDIA GPUs, and more vendors (like AMD
and Apple chips). The end goal is to target most GPUs.

Beyond compiling to GPUs, Bend2 also targets several common programming
languages. This allows you to export Bend libraries to Python, JavaScript, Go
and more, and use it natively from inside any other project.

## Examples

Bend has a Python-like syntax, Haskell-like semantics, and Lean-like proofs.

```py
# Computes the distance between two points
def distance(ax: F64, ay: F64, bx: F64, by: F64) -> F64:
  x_dist = ((bx - ax) ** 2.0) 
  y_dist = ((by - ay) ** 2.0)
  return (x_dist + y_dist) ** 0.5

# Prints the distance from (x:0,y:3) to {x:4,y:0}
def main() -> F64:
  return distance(0.0, 3.0, 4.0, 0.0)
```

While this looks similar to a typed Python, the way Bend actually works is much
closer to Haskell - it is a *pure functional language*, meaning algorithms are
written using datatypes, pattern-matching and recursion. This may be harder to
certain audiences, but is necessary for it to offer its advanced features.

```py
# A Binary Tree
type Tree<A: Set>:
  case @Leaf:
    value : A
  case @Node:
    left  : Tree<A>
    right : Tree<A>

# Sums all values in a tree
def sum(tree: Tree<F64>) -> F64:
  match tree:
    case @Leaf{value}:
      return value
    case @Node{left, right}:
      return sum(left) + sum(right)

# Sums the '((1,2),(3,4))' tree
def main() -> F64:
  tree = @Node{
    @Node{@Leaf{1.0}, @Leaf{2.0}},
    @Node{@Leaf{3.0}, @Leaf{4.0}},
  } :: Tree<F64>
  return sum(tree)
```

Bend is also a proof assistant, like Lean. Below, we prove `a+b=b+a`:

```py
# Adds two Natural Numbers
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

# Proof that 'a + b = b + a'
def comm(a: Nat, b: Nat) -> Nat{add(a,b) == add(b,a)}:
  match a:
    case 0n:
      zero_right(b)
    case 1n+ap:
      rewrite comm(ap,b)
      rewrite succ_right(b,ap)
      finally
```

You can run the programs above with `bend file_name.bend`. Make sure to execute
the CLI from the `BendRoot/` directory of your workspace, as the import system
expects all paths to be relative to that root.

## Using SupGen: an automatic programmer and prover

TODO: continue...

**THIS REPOSITORY IS A WORK IN PROGRESS**
